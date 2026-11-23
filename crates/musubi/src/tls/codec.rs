//! Bounded enrollment codecs, also compiled directly into the enrollment fuzz target.

use anyhow::ensure;
use base64::Engine as _;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use bip39::{Language, Mnemonic};
use serde::{Deserialize, Serialize};
use x509_parser::prelude::{FromDer as _, X509CertificationRequest};

pub(super) const MAX_EXCHANGE: usize = 16 * 1024;
const MAX_LABEL: usize = 255;

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct InvitationKey {
    pub version: u8,
    pub id: String,
    pub pin: String,
    pub secret: String,
}

pub(super) fn invitation_id(secret: &str) -> anyhow::Result<String> {
    ensure!(valid_token(secret), "invalid TLS invitation");
    let mut context = ring::digest::Context::new(&ring::digest::SHA256);
    context.update(b"musubi invitation ID v1\0");
    context.update(&URL_SAFE_NO_PAD.decode(secret)?);
    Ok(URL_SAFE_NO_PAD.encode(context.finish().as_ref()))
}

/// Two English BIP-39 blocks: full certificate pin, then full enrollment secret.
pub(super) fn encode_key(key: &InvitationKey) -> anyhow::Result<String> {
    ensure!(key.version == 1, "invalid TLS invitation");
    ensure!(
        key.id == invitation_id(&key.secret)?,
        "invalid TLS invitation"
    );
    let mut blocks = Vec::with_capacity(2);
    for token in [&key.pin, &key.secret] {
        ensure!(valid_token(token), "invalid TLS invitation");
        let bytes = URL_SAFE_NO_PAD.decode(token)?;
        blocks.push(Mnemonic::from_entropy_in(Language::English, &bytes)?.to_string());
    }
    Ok(blocks.join(" "))
}

pub(super) fn decode_key(text: &str) -> anyhow::Result<InvitationKey> {
    const INVALID: &str = "expected a 48-word join phrase; run `musubi hub invite` on the \
        hub's machine for a new one";
    ensure!(text.len() <= 1024, INVALID);
    let words: Vec<_> = text.split_ascii_whitespace().collect();
    ensure!(words.len() == 48, INVALID);
    let decode_block = |words: &[&str]| -> anyhow::Result<String> {
        let phrase = words.join(" ").to_ascii_lowercase();
        let mnemonic = Mnemonic::parse_in_normalized(Language::English, &phrase)
            .map_err(|_| anyhow::anyhow!(INVALID))?;
        Ok(URL_SAFE_NO_PAD.encode(mnemonic.to_entropy()))
    };
    let pin = decode_block(&words[..24])?;
    let secret = decode_block(&words[24..])?;
    Ok(InvitationKey {
        version: 1,
        id: invitation_id(&secret)?,
        pin,
        secret,
    })
}

pub(super) fn valid_token(text: &str) -> bool {
    text.len() == 43 && URL_SAFE_NO_PAD.decode(text).is_ok_and(|b| b.len() == 32)
}

/// Descriptive metadata only: labels never select or authorize a client.
pub(super) fn sanitize_label(label: &str) -> anyhow::Result<String> {
    ensure!(
        label.len() <= MAX_LABEL,
        "TLS client label must not exceed 255 bytes"
    );
    let label = label
        .trim()
        .chars()
        .map(|c| {
            if c.is_control()
                || matches!(
                    c,
                    '\u{200b}'..='\u{200f}'
                        | '\u{2028}'..='\u{202e}'
                        | '\u{2060}'..='\u{206f}'
                        | '\u{feff}'
                )
            {
                '?'
            } else {
                c
            }
        })
        .collect::<String>();
    ensure!(!label.is_empty(), "TLS client label must not be empty");
    Ok(label)
}

pub(super) fn csr_label(csr: &[u8]) -> anyhow::Result<String> {
    ensure!(csr.len() <= MAX_EXCHANGE / 2, "invalid enrollment request");
    let (rest, request) = X509CertificationRequest::from_der(csr)
        .map_err(|_| anyhow::anyhow!("invalid enrollment request"))?;
    ensure!(rest.is_empty(), "invalid enrollment request");
    request
        .verify_signature()
        .map_err(|_| anyhow::anyhow!("invalid enrollment request"))?;
    let mut names = request
        .certification_request_info
        .subject
        .iter_common_name();
    let name = names
        .next()
        .ok_or_else(|| anyhow::anyhow!("invalid enrollment client label"))?;
    ensure!(names.next().is_none(), "invalid enrollment client label");
    let label = name
        .as_str()
        .map_err(|_| anyhow::anyhow!("invalid enrollment client label"))?;
    sanitize_label(label)
}

pub(super) fn verify_csr(csr: &[u8]) -> anyhow::Result<()> {
    csr_label(csr).map(|_| ())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Enrollment {
    pub version: u8,
    pub id: String,
    pub secret: String,
    pub csr: Vec<u8>,
}

pub(super) fn decode_enrollment(bytes: &[u8]) -> anyhow::Result<Enrollment> {
    ensure!(bytes.len() <= MAX_EXCHANGE, "invalid enrollment request");
    let request: Enrollment =
        serde_json::from_slice(bytes).map_err(|_| anyhow::anyhow!("invalid enrollment request"))?;
    ensure!(
        request.version == 1 && valid_token(&request.id) && valid_token(&request.secret),
        "invalid enrollment request"
    );
    verify_csr(&request.csr)?;
    Ok(request)
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct EnrollmentReply {
    pub certificate: Option<Vec<u8>>,
}

pub(super) fn decode_reply(bytes: &[u8]) -> anyhow::Result<EnrollmentReply> {
    ensure!(bytes.len() <= MAX_EXCHANGE, "invalid enrollment reply");
    let reply: EnrollmentReply =
        serde_json::from_slice(bytes).map_err(|_| anyhow::anyhow!("invalid enrollment reply"))?;
    if let Some(cert) = &reply.certificate {
        let (rest, _) = x509_parser::parse_x509_certificate(cert)
            .map_err(|_| anyhow::anyhow!("invalid enrollment reply"))?;
        ensure!(rest.is_empty(), "invalid enrollment reply");
    }
    Ok(reply)
}

/// No sockets, configuration, or state dependencies; all peer-controlled decoders run here.
#[cfg(any(fuzzing, test))]
pub fn fuzz(bytes: &[u8]) {
    let _request = decode_enrollment(bytes);
    let _reply = decode_reply(bytes);
    let _csr = verify_csr(bytes);
    if let Ok(text) = std::str::from_utf8(bytes) {
        if let Ok(key) = decode_key(text) {
            let phrase = encode_key(&key).expect("a decoded invitation must encode");
            let decoded = decode_key(&phrase).expect("an encoded invitation must decode");
            assert_eq!(decoded.id, key.id);
            assert_eq!(decoded.pin, key.pin);
            assert_eq!(decoded.secret, key.secret);
        }
        let _label = sanitize_label(text);
    }
}
