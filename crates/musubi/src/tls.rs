//! Direct TLS connections. Anonymous peers have only a short, bounded enrollment exchange;
//! sync streams require both proof of a client key and current, persisted authorization.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, RwLock};
use std::time::Duration;

use anyhow::{Context as _, ensure};
use async_trait::async_trait;
use base64::Engine as _;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use musubi_transport::stream::{Connector, Reader, Writer};
use notify::Watcher as _;
use rcgen::{CertificateParams, CertificateSigningRequestParams, IsCa, KeyPair};
use ring::digest::{SHA256, digest};
use ring::rand::{SecureRandom as _, SystemRandom};
use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::pki_types::{
    CertificateDer, CertificateSigningRequestDer, PrivateKeyDer, PrivatePkcs8KeyDer, ServerName,
    UnixTime,
};
use rustls::server::danger::{ClientCertVerified, ClientCertVerifier};
use rustls::{DigitallySignedStruct, DistinguishedName, RootCertStore, SignatureScheme};
use serde::{Deserialize, Serialize};
use tokio::io::{AsyncRead, AsyncReadExt as _, AsyncWrite, AsyncWriteExt as _};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{OwnedSemaphorePermit, Semaphore, watch};
use tokio::task::JoinSet;
use tokio::time::{timeout, timeout_at};
use tokio_rustls::{TlsAcceptor, TlsConnector};

mod codec;

use codec::{
    Enrollment, EnrollmentReply, InvitationKey, MAX_EXCHANGE, csr_label, decode_enrollment,
    decode_key, decode_reply, encode_key, invitation_id, sanitize_label,
};

pub fn key_block(key: &str) -> String {
    let words: Vec<_> = key.split_ascii_whitespace().collect();
    words
        .chunks(6)
        .map(|line| format!("  {}", line.join(" ")))
        .collect::<Vec<_>>()
        .join("\n")
}

const DEADLINE: Duration = Duration::from_secs(10);
const POLL: Duration = Duration::from_millis(100);
const MAX_AUTHENTICATED_SESSIONS: usize = 128;
const MAX_HANDSHAKES: usize = 32;
const MAX_UNAUTHENTICATED_SESSIONS: usize = 16;
const ENROLL: &[u8; 8] = b"MSBENR01";
const SYNC: &[u8; 8] = b"MSBSYN01";

fn authorization_event_relevant(event: &notify::Result<notify::Event>) -> bool {
    match event {
        Ok(event) => {
            !matches!(event.kind, notify::EventKind::Access(_))
                && (event.paths.is_empty()
                    || event.paths.iter().any(|path| {
                        path.file_name()
                            .is_some_and(|name| name == "authorization.json")
                    }))
        }
        Err(_) => true,
    }
}

async fn accept_with_retry<T, F, Fut>(mut accept: F) -> T
where
    F: FnMut() -> Fut,
    Fut: Future<Output = io::Result<T>>,
{
    let mut backoff =
        crate::backoff::Backoff::new(Duration::from_millis(10), Duration::from_millis(100));
    loop {
        match accept().await {
            Ok(accepted) => return accepted,
            Err(err) => {
                let pause = backoff.next();
                tracing::warn!("cannot accept a TLS connection; retrying in {pause:?}: {err}");
                tokio::time::sleep(pause).await;
            }
        }
    }
}

#[derive(Clone, Copy)]
struct SessionLimits {
    handshakes: usize,
    unauthenticated: usize,
    authenticated: usize,
    authentication_deadline: Duration,
}

impl Default for SessionLimits {
    fn default() -> Self {
        Self {
            handshakes: MAX_HANDSHAKES,
            unauthenticated: MAX_UNAUTHENTICATED_SESSIONS,
            authenticated: MAX_AUTHENTICATED_SESSIONS,
            authentication_deadline: DEADLINE,
        }
    }
}

struct ConnectionAdmission {
    handshake: OwnedSemaphorePermit,
    unauthenticated: Arc<Semaphore>,
    authenticated: Arc<Semaphore>,
    deadline: tokio::time::Instant,
}

pub fn is_tls(hub: &str) -> bool {
    hub.starts_with("musubi://")
}

/// Only an authority is accepted: no credentials, path, query or implicit port.
pub fn validate_endpoint(hub: &str) -> anyhow::Result<()> {
    endpoint(hub).map(|_| ())
}

fn endpoint(hub: &str) -> anyhow::Result<(String, String)> {
    let authority = hub
        .strip_prefix("musubi://")
        .context("a TLS hub must be musubi://host:port")?;
    ensure!(
        !authority.is_empty()
            && !authority
                .chars()
                .any(|c| c.is_whitespace() || "/?#@\\".contains(c)),
        "a TLS hub must contain only a host and explicit port"
    );
    let (host, port) = if let Some(rest) = authority.strip_prefix('[') {
        let (ip, port) = rest
            .split_once("]:")
            .context("an IPv6 TLS hub must be musubi://[address]:port")?;
        ip.parse::<std::net::Ipv6Addr>()
            .context("invalid IPv6 TLS hub address")?;
        (ip, port)
    } else {
        let (host, port) = authority
            .rsplit_once(':')
            .context("a TLS hub needs an explicit port")?;
        ensure!(
            !host.contains([':', '[', ']']),
            "bracket an IPv6 TLS hub address"
        );
        (host, port)
    };
    ensure!(!host.is_empty(), "a TLS hub needs a host");
    let port: u16 = port.parse().context("invalid TLS hub port")?;
    ensure!(port != 0, "a TLS hub port must not be zero");
    ServerName::try_from(host.to_owned()).context("invalid TLS hub host")?;
    let address = if host.contains(':') {
        format!("[{host}]:{port}")
    } else {
        format!("{}:{port}", host.to_ascii_lowercase())
    };
    Ok((host.to_ascii_lowercase(), address))
}

fn hash(bytes: &[u8]) -> String {
    URL_SAFE_NO_PAD.encode(digest(&SHA256, bytes).as_ref())
}

fn secret_tag(secret: &str) -> String {
    let key = ring::hmac::Key::new(ring::hmac::HMAC_SHA256, b"musubi enrollment secret v1");
    URL_SAFE_NO_PAD.encode(ring::hmac::sign(&key, secret.as_bytes()).as_ref())
}

fn verify_secret(secret: &str, tag: &str) -> bool {
    let key = ring::hmac::Key::new(ring::hmac::HMAC_SHA256, b"musubi enrollment secret v1");
    URL_SAFE_NO_PAD
        .decode(tag)
        .is_ok_and(|tag| ring::hmac::verify(&key, secret.as_bytes(), &tag).is_ok())
}

fn random() -> anyhow::Result<String> {
    let mut bytes = [0; 32];
    SystemRandom::new()
        .fill(&mut bytes)
        .map_err(|_| anyhow::anyhow!("cryptographic random source failed"))?;
    Ok(URL_SAFE_NO_PAD.encode(bytes))
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Invite {
    secret_hash: String,
    single_use: bool,
    // Rotating, single-use invitations retain their current secret in hub state.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    secret: Option<String>,
}

#[derive(Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Authorization {
    invitations: BTreeMap<String, Invite>,
    // IDs are the SHA256 fingerprint of the issued certificate.
    clients: BTreeMap<String, String>,
}

fn enrollment_in_time(deadline: Option<tokio::time::Instant>) -> anyhow::Result<()> {
    ensure!(
        deadline.is_none_or(|deadline| tokio::time::Instant::now() < deadline),
        "TLS enrollment timed out"
    );
    Ok(())
}

fn valid_invitation<'a>(
    state: &'a Authorization,
    id: &str,
    secret: &str,
) -> anyhow::Result<&'a Invite> {
    let invite = state
        .invitations
        .get(id)
        .context("TLS enrollment was refused")
        .map_err(|err| {
            crate::ui::with_hint(
                err,
                "Run `musubi hub invite` on the hub's machine for a new invitation.",
            )
        })?;
    ensure!(
        verify_secret(secret, &invite.secret_hash),
        "enrollment refused"
    );
    Ok(invite)
}

#[derive(Serialize, Deserialize)]
struct Identity {
    server_cert: Vec<u8>,
    server_key: Vec<u8>,
    ca_cert_pem: String,
    ca_key_pem: String,
}

impl Identity {
    fn generate() -> anyhow::Result<Self> {
        let server_key = KeyPair::generate()?;
        let server = CertificateParams::new(vec!["musubi".to_owned()])?.self_signed(&server_key)?;
        let ca_key = KeyPair::generate()?;
        let mut params = CertificateParams::new(Vec::<String>::new())?;
        params.is_ca = IsCa::Ca(rcgen::BasicConstraints::Unconstrained);
        params.key_usages = vec![rcgen::KeyUsagePurpose::KeyCertSign];
        let ca = params.self_signed(&ca_key)?;
        Ok(Self {
            server_cert: server.der().to_vec(),
            server_key: server_key.serialize_der(),
            ca_cert_pem: ca.pem(),
            ca_key_pem: ca_key.serialize_pem(),
        })
    }

    fn issue(&self, csr: &[u8]) -> anyhow::Result<(Vec<u8>, String)> {
        // Verify the CSR's signature explicitly, before taking or consuming any invitation.
        let label = csr_label(csr)?;
        let key = KeyPair::from_pem(&self.ca_key_pem)?;
        let ca = CertificateParams::from_ca_cert_pem(&self.ca_cert_pem)?.self_signed(&key)?;
        let mut request =
            CertificateSigningRequestParams::from_der(&CertificateSigningRequestDer::from(csr))?;
        // The peer chooses its public key and display label, never certificate permissions
        // or authorization identity. Only the certificate fingerprint authorizes a client.
        request.params = CertificateParams::new(Vec::<String>::new())?;
        request.params.distinguished_name = rcgen::DistinguishedName::new();
        request
            .params
            .distinguished_name
            .push(rcgen::DnType::CommonName, label.clone());
        request.params.extended_key_usages = vec![rcgen::ExtendedKeyUsagePurpose::ClientAuth];
        request.params.key_usages = vec![rcgen::KeyUsagePurpose::DigitalSignature];
        Ok((request.signed_by(&ca, &key)?.der().to_vec(), label))
    }
}

struct Cached {
    state: Authorization,
}

pub struct Hub {
    dir: PathBuf,
    identity: Identity,
    authorized: Arc<RwLock<Cached>>,
    // A local update wakes sessions without waiting for the cross-process poll.
    changed: watch::Sender<u64>,
}

impl Hub {
    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        let dir = dir.join("tls");
        crate::socket::create_private_dir(&dir)?;
        let _lock = crate::lock::lock(&dir.join("state.lock"))?;
        let identity_path = dir.join("identity.json");
        let identity = match fs::read(&identity_path) {
            Ok(bytes) => serde_json::from_slice(&bytes).context("invalid TLS hub identity")?,
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                let identity = Identity::generate()?;
                crate::config::write_private(&identity_path, &serde_json::to_vec(&identity)?)?;
                identity
            }
            Err(e) => return Err(e).context("reading TLS hub identity"),
        };
        let state_path = dir.join("authorization.json");
        if !state_path.exists() {
            crate::config::write_private(
                &state_path,
                &serde_json::to_vec(&Authorization::default())?,
            )?;
        }
        let state = read_authorization(&state_path)?;
        let (changed, _) = watch::channel(0);
        Ok(Self {
            dir,
            identity,
            authorized: Arc::new(RwLock::new(Cached { state })),
            changed,
        })
    }

    fn update<T>(
        &self,
        change: impl FnOnce(&mut Authorization) -> anyhow::Result<T>,
    ) -> anyhow::Result<T> {
        let _lock = crate::lock::lock(&self.dir.join("state.lock"))?;
        let path = self.dir.join("authorization.json");
        let mut state = read_authorization(&path)?;
        let before = serde_json::to_vec(&state)?;
        let result = change(&mut state)?;
        let after = serde_json::to_vec(&state)?;
        if before != after {
            crate::config::write_private(&path, &after)?;
        }
        *self
            .authorized
            .write()
            .map_err(|_| anyhow::anyhow!("TLS authorization lock poisoned"))? = Cached { state };
        if before != after {
            self.changed
                .send_modify(|epoch| *epoch = epoch.wrapping_add(1));
        }
        Ok(result)
    }

    fn refresh(&self) -> anyhow::Result<()> {
        let path = self.dir.join("authorization.json");
        // State changes replace the file atomically. The lock also serializes simultaneous
        // refreshes with CLI updates. Timestamps aren't evidence of unchanged authorization:
        // filesystems can give separate updates the same timestamp. The hub reloads once per
        // timer/notification and at connection admission, never on a sync-message path.
        let _lock = crate::lock::lock(&self.dir.join("state.lock"))?;
        let state = read_authorization(&path)?;
        let mut cached = self
            .authorized
            .write()
            .map_err(|_| anyhow::anyhow!("TLS authorization lock poisoned"))?;
        if cached.state != state {
            cached.state = state;
            self.changed
                .send_modify(|epoch| *epoch = epoch.wrapping_add(1));
        }
        Ok(())
    }

    async fn reload_authorization(self: &Arc<Self>) -> anyhow::Result<()> {
        let hub = self.clone();
        tokio::task::spawn_blocking(move || hub.refresh())
            .await
            .context("TLS authorization reload task stopped")?
    }

    pub fn invite(&self, single_use: bool) -> anyhow::Result<(String, String)> {
        let secret = random()?;
        let id = invitation_id(&secret)?;
        self.update(|state| {
            ensure!(
                !state.invitations.contains_key(&id),
                "cannot generate a fresh TLS invitation ID"
            );
            state.invitations.insert(
                id.clone(),
                Invite {
                    secret_hash: secret_tag(&secret),
                    single_use,
                    secret: single_use.then(|| secret.clone()),
                },
            );
            Ok(())
        })?;
        let key = InvitationKey {
            version: 1,
            id: id.clone(),
            pin: hash(&self.identity.server_cert),
            secret,
        };
        Ok((id, encode_key(&key)?))
    }

    pub fn revoke_invite(&self, id: &str) -> anyhow::Result<()> {
        self.update(|state| {
            ensure!(
                state.invitations.remove(id).is_some(),
                "unknown TLS invitation ID"
            );
            Ok(())
        })
    }

    pub fn clients(&self) -> anyhow::Result<Vec<(String, String)>> {
        self.refresh()?;
        let cached = self
            .authorized
            .read()
            .map_err(|_| anyhow::anyhow!("TLS authorization lock poisoned"))?;
        cached
            .state
            .clients
            .iter()
            .map(|(id, label)| Ok((id.clone(), sanitize_label(label)?)))
            .collect()
    }

    pub fn invitations(&self) -> anyhow::Result<Vec<(String, bool)>> {
        self.refresh()?;
        Ok(self
            .authorized
            .read()
            .map_err(|_| anyhow::anyhow!("TLS authorization lock poisoned"))?
            .state
            .invitations
            .iter()
            .map(|(id, invite)| (id.clone(), invite.single_use))
            .collect())
    }

    pub fn revoke_client(&self, id: &str) -> anyhow::Result<()> {
        self.update(|state| {
            ensure!(state.clients.remove(id).is_some(), "unknown TLS client ID");
            Ok(())
        })
    }

    #[cfg(test)]
    fn enroll(&self, request: Enrollment) -> anyhow::Result<Vec<u8>> {
        self.enroll_with_deadline(request, None)
    }

    fn enroll_before(
        &self,
        request: Enrollment,
        deadline: tokio::time::Instant,
    ) -> anyhow::Result<Vec<u8>> {
        self.enroll_with_deadline(request, Some(deadline))
    }

    fn enroll_with_deadline(
        &self,
        request: Enrollment,
        deadline: Option<tokio::time::Instant>,
    ) -> anyhow::Result<Vec<u8>> {
        // Refuse an invalid secret before parsing or signing the untrusted CSR. Recheck below
        // while committing, since concurrent requests can pass this first check together.
        enrollment_in_time(deadline)?;
        self.update(|state| valid_invitation(state, &request.id, &request.secret).map(drop))?;
        enrollment_in_time(deadline)?;
        let (certificate, label) = self.identity.issue(&request.csr)?;
        self.update(|state| {
            enrollment_in_time(deadline)?;
            let single_use = valid_invitation(state, &request.id, &request.secret)?.single_use;
            if single_use {
                let next_secret = random()?;
                let next_id = invitation_id(&next_secret)?;
                ensure!(
                    !state.invitations.contains_key(&next_id),
                    "cannot generate a fresh TLS invitation ID"
                );
                ensure!(
                    next_secret != request.secret,
                    "cannot generate a fresh TLS enrollment secret"
                );
                state.invitations.remove(&request.id);
                state.invitations.insert(
                    next_id,
                    Invite {
                        secret_hash: secret_tag(&next_secret),
                        single_use: true,
                        secret: Some(next_secret),
                    },
                );
            }
            state.clients.insert(hash(&certificate), label);
            Ok(())
        })?;
        Ok(certificate)
    }

    fn authorized(&self, id: &str) -> bool {
        self.authorized
            .read()
            .is_ok_and(|state| state.state.clients.contains_key(id))
    }

    fn server_config(self: &Arc<Self>) -> anyhow::Result<rustls::ServerConfig> {
        let ca_key = KeyPair::from_pem(&self.identity.ca_key_pem)?;
        let ca = CertificateParams::from_ca_cert_pem(&self.identity.ca_cert_pem)?
            .self_signed(&ca_key)?;
        let mut roots = RootCertStore::empty();
        roots.add(ca.der().clone())?;
        let verifier = rustls::server::WebPkiClientVerifier::builder_with_provider(
            Arc::new(roots),
            Arc::new(rustls::crypto::ring::default_provider()),
        )
        .allow_unauthenticated()
        .build()?;
        let verifier = AuthorizedVerifier {
            inner: verifier,
            hub: self.clone(),
        };
        let mut config = rustls::ServerConfig::builder_with_provider(Arc::new(
            rustls::crypto::ring::default_provider(),
        ))
        .with_safe_default_protocol_versions()?
        .with_client_cert_verifier(Arc::new(verifier))
        .with_single_cert(
            vec![CertificateDer::from(self.identity.server_cert.clone())],
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(self.identity.server_key.clone())),
        )?;
        config.session_storage = Arc::new(rustls::server::NoServerSessionStorage {});
        config.send_tls13_tickets = 0;
        Ok(config)
    }

    pub async fn serve(
        self: Arc<Self>,
        listener: TcpListener,
        transport: Arc<dyn musubi_transport::Transport>,
    ) -> anyhow::Result<()> {
        self.serve_with_limits(listener, transport, SessionLimits::default())
            .await
    }

    async fn serve_with_limits(
        self: Arc<Self>,
        listener: TcpListener,
        transport: Arc<dyn musubi_transport::Transport>,
        limits: SessionLimits,
    ) -> anyhow::Result<()> {
        let acceptor = TlsAcceptor::from(Arc::new(self.server_config()?));
        let handshakes = Arc::new(Semaphore::new(limits.handshakes));
        let unauthenticated = Arc::new(Semaphore::new(limits.unauthenticated));
        let authenticated = Arc::new(Semaphore::new(limits.authenticated));
        let mut sessions = JoinSet::new();
        let (accepted, mut incoming) = tokio::sync::mpsc::channel(1);
        let _accepting = tokio::spawn(async move {
            loop {
                let connection = accept_with_retry(|| listener.accept()).await;
                if accepted
                    .send((connection, tokio::time::Instant::now()))
                    .await
                    .is_err()
                {
                    break;
                }
            }
        });
        let mut poll = tokio::time::interval(POLL);
        poll.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        let (changes, mut changed) = tokio::sync::mpsc::channel(1);
        let mut watcher =
            notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
                if authorization_event_relevant(&event) {
                    let _sent = changes.try_send(event.map(|_| ()));
                }
            })?;
        // Watch the directory, not the file replaced by rare authorization updates.
        watcher.watch(&self.dir, notify::RecursiveMode::NonRecursive)?;
        let mut authorization_available = true;
        let mut watcher_available = true;
        let mut listener_available = true;
        loop {
            tokio::select! {
                event = changed.recv(), if watcher_available => {
                    match event {
                        Some(Ok(())) => match self.reload_authorization().await {
                            Ok(()) => authorization_available = true,
                            Err(err) => {
                                tracing::warn!("TLS authorization is unavailable: {err:#}");
                                sessions.abort_all();
                                authorization_available = false;
                            }
                        },
                        Some(Err(err)) => {
                            tracing::warn!("TLS authorization watcher failed: {err:#}");
                            sessions.abort_all();
                            authorization_available = false;
                            watcher_available = false;
                        }
                        None => {
                            tracing::warn!("TLS authorization watcher stopped");
                            sessions.abort_all();
                            authorization_available = false;
                            watcher_available = false;
                        }
                    }
                }
                _ = poll.tick(), if !authorization_available || !watcher_available => {
                    match self.reload_authorization().await {
                        Ok(()) => authorization_available = true,
                        Err(err) => {
                            tracing::warn!("TLS authorization is unavailable: {err:#}");
                            sessions.abort_all();
                        }
                    }
                }
                Some(_) = sessions.join_next(), if !sessions.is_empty() => {}
                accepted = incoming.recv(), if authorization_available && listener_available => {
                    let Some(((socket, _), accepted_at)) = accepted else {
                        tracing::error!("TLS listener stopped accepting connections");
                        listener_available = false;
                        continue;
                    };
                    let Ok(handshake) = handshakes.clone().try_acquire_owned() else {
                        tracing::debug!("refusing a TLS connection while handshake capacity is full");
                        continue;
                    };
                    let deadline = accepted_at + limits.authentication_deadline;
                    // A separate administration process can revoke a client just before this
                    // accept. Reload off the async worker before admitting its certificate.
                    let reloading = tokio::task::spawn_blocking({
                        let hub = self.clone();
                        move || (hub.refresh(), handshake)
                    });
                    let handshake = match timeout_at(deadline, reloading).await {
                        Ok(Ok((Ok(()), handshake))) => handshake,
                        Ok(Ok((Err(err), _handshake))) => {
                            tracing::warn!("TLS authorization is unavailable: {err:#}");
                            sessions.abort_all();
                            authorization_available = false;
                            continue;
                        }
                        Ok(Err(err)) => {
                            tracing::warn!("TLS authorization reload task stopped: {err}");
                            sessions.abort_all();
                            authorization_available = false;
                            continue;
                        }
                        Err(_) => {
                            tracing::warn!("TLS authorization reload timed out");
                            sessions.abort_all();
                            authorization_available = false;
                            continue;
                        }
                    };
                    let hub = self.clone();
                    let acceptor = acceptor.clone();
                    let transport = transport.clone();
                    let unauthenticated = unauthenticated.clone();
                    let authenticated = authenticated.clone();
                    sessions.spawn(async move {
                        hub.connection(
                            socket,
                            acceptor,
                            transport,
                            ConnectionAdmission {
                                handshake,
                                unauthenticated,
                                authenticated,
                                deadline,
                            },
                        )
                        .await
                    });
                }
            }
        }
    }

    async fn connection(
        self: Arc<Self>,
        socket: TcpStream,
        acceptor: TlsAcceptor,
        transport: Arc<dyn musubi_transport::Transport>,
        admission: ConnectionAdmission,
    ) -> anyhow::Result<()> {
        let ConnectionAdmission {
            handshake,
            unauthenticated,
            authenticated,
            deadline,
        } = admission;
        let admitted = timeout_at(deadline, async {
            let mut stream = acceptor.accept(socket).await?;
            let id = stream
                .get_ref()
                .1
                .peer_certificates()
                .and_then(|certs| certs.first())
                .map(|cert| hash(cert.as_ref()));
            let mut mode = [0; 8];
            stream.read_exact(&mut mode).await?;
            if &mode == ENROLL && id.is_none() {
                let permit = unauthenticated
                    .try_acquire_owned()
                    .context("too many unauthenticated TLS connections")?;
                drop(handshake);
                let bytes = read_exchange(&mut stream).await?;
                let certificate = match decode_enrollment(&bytes) {
                    Ok(request) => {
                        let hub = self.clone();
                        tokio::task::spawn_blocking(move || {
                            let _permit = permit;
                            hub.enroll_before(request, deadline)
                        })
                        .await
                        .context("TLS enrollment task stopped")?
                    }
                    Err(err) => {
                        drop(permit);
                        Err(err)
                    }
                };
                let response = match certificate {
                    Ok(certificate) => EnrollmentReply {
                        certificate: Some(certificate),
                    },
                    Err(_) => EnrollmentReply { certificate: None },
                };
                write_exchange(&mut stream, &serde_json::to_vec(&response)?).await?;
                stream.shutdown().await?;
                return Ok::<_, anyhow::Error>(None);
            }
            ensure!(
                &mode == SYNC,
                "TLS connection is not an authenticated sync stream"
            );
            let id = id.context("TLS sync needs an enrolled client certificate")?;
            let changed = self.changed.subscribe();
            ensure!(self.authorized(&id), "TLS client was revoked");
            let permit = authenticated
                .try_acquire_owned()
                .context("too many authenticated TLS connections")?;
            drop(handshake);
            Ok(Some((stream, id, changed, permit)))
        })
        .await
        .context("TLS authentication timed out")??;
        let Some((stream, id, mut changed, _permit)) = admitted else {
            return Ok(());
        };
        let (reader, writer) = tokio::io::split(stream);
        let serve = musubi_transport::stream::serve(transport, reader, writer);
        tokio::pin!(serve);
        loop {
            tokio::select! {
                result = &mut serve => return result.map_err(Into::into),
                result = changed.changed() => {
                    result?;
                    ensure!(self.authorized(&id), "TLS client was revoked");
                }
            }
        }
    }
}

fn read_authorization(path: &Path) -> anyhow::Result<Authorization> {
    let state: Authorization =
        serde_json::from_slice(&fs::read(path)?).context("invalid TLS hub authorization state")?;
    for (id, invite) in &state.invitations {
        ensure!(
            codec::valid_token(id) && codec::valid_token(&invite.secret_hash),
            "invalid stored TLS invitation"
        );
        ensure!(
            invite.single_use == invite.secret.is_some(),
            "invalid stored TLS invitation secret"
        );
        if let Some(secret) = &invite.secret {
            ensure!(
                invitation_id(secret)? == *id && verify_secret(secret, &invite.secret_hash),
                "invalid stored single-use TLS invitation"
            );
        }
    }
    Ok(state)
}

/// Current rotating enrollment keys for tests of single-use invitation replacement.
#[cfg(test)]
fn invitation_status(dir: &Path) -> anyhow::Result<(Vec<String>, bool)> {
    let dir = dir.join("tls");
    match fs::metadata(&dir) {
        Ok(metadata) => ensure!(metadata.is_dir(), "TLS hub state is not a directory"),
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok((Vec::new(), false)),
        Err(e) => return Err(e).context("reading TLS hub state directory"),
    }
    let _lock = crate::lock::lock(&dir.join("state.lock"))?;
    let identity: Identity = serde_json::from_slice(&fs::read(dir.join("identity.json"))?)
        .context("invalid TLS hub identity")?;
    let state = read_authorization(&dir.join("authorization.json"))?;
    let pin = hash(&identity.server_cert);
    let reusable = state.invitations.values().any(|invite| !invite.single_use);
    let keys = state
        .invitations
        .iter()
        .filter(|(_, invite)| invite.single_use)
        .map(|(id, invite)| {
            let secret = invite
                .secret
                .as_ref()
                .context("missing stored single-use TLS invitation secret")?;
            let key = InvitationKey {
                version: 1,
                id: id.clone(),
                pin: pin.clone(),
                secret: secret.clone(),
            };
            encode_key(&key)
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    Ok((keys, reusable))
}

#[cfg(test)]
fn single_use_keys(dir: &Path) -> anyhow::Result<Vec<String>> {
    Ok(invitation_status(dir)?.0)
}

struct AuthorizedVerifier {
    inner: Arc<dyn ClientCertVerifier>,
    hub: Arc<Hub>,
}

impl std::fmt::Debug for AuthorizedVerifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("AuthorizedVerifier")
    }
}

impl ClientCertVerifier for AuthorizedVerifier {
    fn client_auth_mandatory(&self) -> bool {
        false
    }
    fn root_hint_subjects(&self) -> &[DistinguishedName] {
        self.inner.root_hint_subjects()
    }
    fn verify_client_cert(
        &self,
        end: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        now: UnixTime,
    ) -> Result<ClientCertVerified, rustls::Error> {
        self.inner.verify_client_cert(end, intermediates, now)?;
        if !self.hub.authorized(&hash(end.as_ref())) {
            return Err(rustls::Error::General(
                "TLS client is not authorized; enroll again".to_owned(),
            ));
        }
        Ok(ClientCertVerified::assertion())
    }
    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls12_signature(message, cert, dss)
    }
    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls13_signature(message, cert, dss)
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.inner.supported_verify_schemes()
    }
}

#[derive(Debug)]
struct PinnedVerifier {
    pin: String,
}

impl ServerCertVerifier for PinnedVerifier {
    fn verify_server_cert(
        &self,
        end: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _name: &ServerName<'_>,
        _ocsp: &[u8],
        _now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        if hash(end.as_ref()) != self.pin {
            return Err(rustls::Error::General(
                "TLS hub identity does not match the invitation; obtain a new invitation"
                    .to_owned(),
            ));
        }
        Ok(ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }
    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

async fn read_exchange(stream: &mut (impl AsyncRead + Unpin)) -> anyhow::Result<Vec<u8>> {
    let len = usize::try_from(stream.read_u32().await?)?;
    ensure!(len <= MAX_EXCHANGE, "TLS enrollment message too large");
    let mut bytes = vec![0; len];
    stream.read_exact(&mut bytes).await?;
    Ok(bytes)
}

async fn write_exchange(
    stream: &mut (impl AsyncWrite + Unpin),
    bytes: &[u8],
) -> anyhow::Result<()> {
    ensure!(
        bytes.len() <= MAX_EXCHANGE,
        "TLS enrollment message too large"
    );
    stream.write_u32(u32::try_from(bytes.len())?).await?;
    stream.write_all(bytes).await?;
    stream.flush().await?;
    Ok(())
}

#[derive(Clone, Serialize, Deserialize)]
struct Credentials {
    pin: String,
    certificate: Vec<u8>,
    private_key: Vec<u8>,
}

fn credential_path(hub: &str) -> anyhow::Result<PathBuf> {
    let (_, address) = endpoint(hub)?;
    Ok(crate::config::state_dir()?
        .join("tls")
        .join(format!("{}.json", hash(address.as_bytes()))))
}

pub fn has_credentials(hub: &str) -> anyhow::Result<bool> {
    match fs::read(credential_path(hub)?) {
        Ok(bytes) => {
            let _credentials: Credentials = serde_json::from_slice(&bytes)
                .context("invalid TLS client credentials")
                .map_err(|err| {
                    crate::ui::with_hint(
                        err,
                        format!(
                            "Run `musubi enroll --hub {}` with a fresh invitation to re-enroll",
                            crate::ui::shell_word(hub)
                        ),
                    )
                })?;
            Ok(true)
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(e).context("reading TLS client credentials"),
    }
}

fn client_config(
    pin: String,
    credentials: Option<Credentials>,
) -> anyhow::Result<rustls::ClientConfig> {
    let builder = rustls::ClientConfig::builder_with_provider(Arc::new(
        rustls::crypto::ring::default_provider(),
    ))
    .with_safe_default_protocol_versions()?
    .dangerous()
    .with_custom_certificate_verifier(Arc::new(PinnedVerifier { pin }));
    let mut config = match credentials {
        Some(credentials) => builder.with_client_auth_cert(
            vec![CertificateDer::from(credentials.certificate)],
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(credentials.private_key)),
        )?,
        None => builder.with_no_client_auth(),
    };
    // Each connection proves both keys afresh; a resumed session must not skip authorization.
    config.resumption = rustls::client::Resumption::disabled();
    Ok(config)
}

async fn dial(
    hub: &str,
    config: rustls::ClientConfig,
) -> anyhow::Result<tokio_rustls::client::TlsStream<TcpStream>> {
    let (host, address) = endpoint(hub)?;
    let socket = TcpStream::connect(address)
        .await
        .context("cannot reach TLS hub")?;
    socket.set_nodelay(true)?;
    TlsConnector::from(Arc::new(config))
        .connect(ServerName::try_from(host)?, socket)
        .await
        .context("TLS hub authentication failed")
        .map_err(|err| {
            crate::ui::with_hint(
                err,
                format!(
                    "Run `musubi enroll --hub {}` with a fresh invitation to re-enroll",
                    crate::ui::shell_word(hub)
                ),
            )
        })
}

/// Explicit enrollment replaces old credentials only after a successful, pinned exchange.
pub async fn prepare(hub: &str, key: &str, label: &str) -> anyhow::Result<()> {
    let credentials = remote_credentials(hub, key, label).await?;
    crate::config::create_state_dir()?;
    let path = credential_path(hub)?;
    crate::socket::create_private_dir(path.parent().context("invalid TLS credential path")?)?;
    let _lock = crate::lock::lock(&path.with_extension("lock"))?;
    let bytes = serde_json::to_vec(&credentials)?;
    match fs::read(&path) {
        Ok(existing) if existing == bytes => {}
        Ok(_) => crate::config::write_private(&path, &bytes)?,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            crate::config::write_private(&path, &bytes)?;
        }
        Err(e) => return Err(e).context("reading TLS client credentials"),
    }
    Ok(())
}

async fn remote_credentials(hub: &str, key: &str, label: &str) -> anyhow::Result<Credentials> {
    validate_endpoint(hub)?;
    let label = sanitize_label(label)?;
    let invitation = decode_key(key)?;
    let private = KeyPair::generate()?;
    let mut params = CertificateParams::new(Vec::<String>::new())?;
    params.distinguished_name = rcgen::DistinguishedName::new();
    params
        .distinguished_name
        .push(rcgen::DnType::CommonName, label);
    let csr = params.serialize_request(&private)?;
    let request = Enrollment {
        version: 1,
        id: invitation.id,
        secret: invitation.secret,
        csr: csr.der().to_vec(),
    };
    let exchange = async {
        // The complete TLS handshake, including its cryptographic signatures, precedes
        // the first write of the secret. No early data or session resumption is enabled.
        let mut stream = dial(hub, client_config(invitation.pin.clone(), None)?).await?;
        stream.write_all(ENROLL).await?;
        write_exchange(&mut stream, &serde_json::to_vec(&request)?).await?;
        let response = decode_reply(&read_exchange(&mut stream).await?)?;
        let certificate = response.certificate.context(
            "TLS enrollment refused; run `musubi hub invite` on the hub's machine \
                 for a new invitation",
        )?;
        let credentials = Credentials {
            pin: invitation.pin,
            certificate,
            private_key: private.serialize_der(),
        };
        // Check that the hub certified the key this client generated, before persisting it.
        client_config(credentials.pin.clone(), Some(credentials.clone()))?;
        Ok::<_, anyhow::Error>(credentials)
    };
    timeout(DEADLINE, exchange)
        .await
        .context("TLS enrollment timed out")?
}

#[derive(Clone)]
pub struct Link {
    hub: String,
    problem: Arc<Mutex<Option<String>>>,
}

impl Link {
    pub fn new(hub: &str) -> anyhow::Result<Self> {
        validate_endpoint(hub)?;
        Ok(Self {
            hub: hub.to_owned(),
            problem: Arc::new(Mutex::new(None)),
        })
    }
    pub fn problem(&self) -> Option<String> {
        self.problem.lock().ok().and_then(|p| p.clone())
    }
}

#[async_trait]
impl Connector for Link {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let connect = async {
            let credentials: Credentials =
                serde_json::from_slice(&fs::read(credential_path(&self.hub)?).context(
                    "no TLS client credentials; run musubi enroll --hub with an invitation",
                )?)
                .context("invalid TLS client credentials")
                .map_err(|err| {
                    crate::ui::with_hint(
                        err,
                        format!(
                            "Run `musubi enroll --hub {}` with a fresh invitation to re-enroll",
                            crate::ui::shell_word(&self.hub)
                        ),
                    )
                })?;
            let mut stream = dial(
                &self.hub,
                client_config(credentials.pin.clone(), Some(credentials))?,
            )
            .await?;
            stream.write_all(SYNC).await?;
            stream.flush().await?;
            // Read one greeting byte so TLS alerts (including revoked clients) are observed
            // here, rather than being mistaken for a successfully connected sync stream.
            let mut first = [0; 1];
            stream
                .read_exact(&mut first)
                .await
                .context("TLS client is not authorized or hub is unavailable")
                .map_err(|err| {
                    crate::ui::with_hint(
                        err,
                        format!(
                            "Run `musubi enroll --hub {}` with a fresh invitation to re-enroll",
                            crate::ui::shell_word(&self.hub)
                        ),
                    )
                })?;
            let (reader, writer) = tokio::io::split(stream);
            let reader = io::Cursor::new(first).chain(reader);
            Ok::<(Reader, Writer), anyhow::Error>((Box::new(reader), Box::new(writer)))
        };
        let result = match timeout(DEADLINE, connect).await {
            Ok(result) => result,
            Err(_) => Err(anyhow::anyhow!(
                "TLS connection timed out; check the hub address"
            )),
        };
        if let Ok(mut problem) = self.problem.lock() {
            *problem = result.as_ref().err().map(|e| format!("{e:#}"));
        }
        result.map_err(|e| io::Error::new(io::ErrorKind::PermissionDenied, format!("{e:#}")))
    }
    fn not_hub(&self, why: &io::Error) {
        if let Ok(mut problem) = self.problem.lock() {
            *problem = Some(format!("TLS hub did not speak the sync protocol: {why}"));
        }
    }
}

/// Pure, bounded decoders for the enrollment fuzz target; never writes state or opens sockets.
#[cfg(any(fuzzing, test))]
pub fn fuzz_enrollment(bytes: &[u8]) {
    codec::fuzz(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::Bytes;
    use musubi_transport::{MemoryNetwork, MemoryTransport, StreamTransport, Transport as _};

    struct Server {
        dir: tempfile::TempDir,
        hub: Arc<Hub>,
        address: String,
        network: MemoryTransport,
        task: tokio::task::JoinHandle<anyhow::Result<()>>,
    }

    impl Drop for Server {
        fn drop(&mut self) {
            self.task.abort();
        }
    }

    impl Server {
        async fn start() -> anyhow::Result<Self> {
            Self::start_with_limits(SessionLimits::default()).await
        }

        async fn start_with_limits(limits: SessionLimits) -> anyhow::Result<Self> {
            let dir = musubi_testutil::tempdir();
            let hub = Arc::new(Hub::open(dir.path())?);
            let listener = TcpListener::bind("127.0.0.1:0").await?;
            let address = format!("musubi://{}", listener.local_addr()?);
            let network = MemoryNetwork::new(1, 1024 * 1024).connect();
            let task = tokio::spawn(hub.clone().serve_with_limits(
                listener,
                Arc::new(network.clone()),
                limits,
            ));
            Ok(Self {
                dir,
                hub,
                address,
                network,
                task,
            })
        }
    }

    fn enrollment_request(key: &str) -> anyhow::Result<Enrollment> {
        let invitation = decode_key(key)?;
        let private = KeyPair::generate()?;
        let csr = CertificateParams::new(Vec::<String>::new())?.serialize_request(&private)?;
        Ok(Enrollment {
            version: 1,
            id: invitation.id,
            secret: invitation.secret,
            csr: csr.der().to_vec(),
        })
    }

    async fn sync_stream(
        address: &str,
        credentials: Credentials,
    ) -> anyhow::Result<tokio_rustls::client::TlsStream<TcpStream>> {
        let mut stream = dial(
            address,
            client_config(credentials.pin.clone(), Some(credentials))?,
        )
        .await?;
        stream.write_all(SYNC).await?;
        let mut greeting = vec![0; musubi_transport::stream::GREETING.len()];
        timeout(Duration::from_secs(2), stream.read_exact(&mut greeting)).await??;
        ensure!(
            greeting == musubi_transport::stream::GREETING,
            "incorrect greeting"
        );
        let _limit = stream.read_u32().await?;
        Ok(stream)
    }

    struct TestConnector {
        address: String,
        credentials: Credentials,
    }

    #[async_trait]
    impl Connector for TestConnector {
        async fn connect(&self) -> io::Result<(Reader, Writer)> {
            let config =
                client_config(self.credentials.pin.clone(), Some(self.credentials.clone()))
                    .map_err(io::Error::other)?;
            let mut stream = dial(&self.address, config)
                .await
                .map_err(io::Error::other)?;
            stream.write_all(SYNC).await?;
            let (reader, writer) = tokio::io::split(stream);
            Ok((Box::new(reader), Box::new(writer)))
        }
    }

    #[test]
    fn mnemonic_invitations_preserve_credentials_and_reject_typing_errors() -> anyhow::Result<()> {
        let key = InvitationKey {
            version: 1,
            id: invitation_id(&URL_SAFE_NO_PAD.encode([0; 32]))?,
            pin: URL_SAFE_NO_PAD.encode([255; 32]),
            secret: URL_SAFE_NO_PAD.encode([0; 32]),
        };
        let zero = format!("{}art", "abandon ".repeat(23));
        let ones = format!("{}vote", "zoo ".repeat(23));
        let short = InvitationKey {
            version: 1,
            id: invitation_id(&key.secret)?,
            pin: key.pin.clone(),
            secret: key.secret.clone(),
        };
        assert_eq!(short.id, "4_ND4NFNj4Qn0DiTFcf9s2dQ141uez5bRSDWQhQpcKg");
        let short_text = format!("{ones} {zero}");
        assert_eq!(encode_key(&short)?, short_text);
        for text in [
            short_text.clone(),
            short_text.to_ascii_uppercase().replace(' ', "\n  "),
        ] {
            let decoded = decode_key(&text)?;
            assert_eq!(decoded.id, short.id);
            assert_eq!(decoded.pin, short.pin);
            assert_eq!(decoded.secret, short.secret);
        }
        for invalid in [
            short_text.replacen("vote", "zoo", 1),
            short_text.replacen("art", "abandon", 1),
            format!("not-a-word {short_text}"),
            format!("{short_text} abandon"),
        ] {
            assert!(decode_key(&invalid).is_err());
        }
        fuzz_enrollment(short_text.as_bytes());
        let expected = format!("{zero} {ones} {zero}");
        assert!(decode_key(&expected).is_err());
        fuzz_enrollment(expected.as_bytes());
        let distinct = InvitationKey {
            version: 1,
            id: invitation_id(&URL_SAFE_NO_PAD.encode([3; 32]))?,
            pin: URL_SAFE_NO_PAD.encode([2; 32]),
            secret: URL_SAFE_NO_PAD.encode([3; 32]),
        };
        let decoded = decode_key(&encode_key(&distinct)?)?;
        assert_eq!(decoded.id, distinct.id);
        assert_eq!(decoded.pin, distinct.pin);
        assert_eq!(decoded.secret, distinct.secret);
        for invalid in [
            expected.replacen("abandon", "notaword", 1),
            expected.replacen("art", "abandon", 1),
            expected.split_once(' ').unwrap().1.to_owned(),
            format!("{expected} abandon"),
            " ".repeat(1025),
        ] {
            assert!(decode_key(&invalid).is_err());
        }
        let err = decode_key("not an invitation")
            .err()
            .context("malformed invitation accepted")?;
        assert!(err.to_string().contains("48-word invitation"));
        assert!(err.to_string().contains("musubi hub invite"));
        Ok(())
    }

    #[test]
    fn endpoints_and_bounded_decoders() -> anyhow::Result<()> {
        for valid in [
            "musubi://example.test:443",
            "musubi://127.0.0.1:123",
            "musubi://[::1]:443",
        ] {
            validate_endpoint(valid)?;
        }
        for invalid in [
            "musubi://host",
            "musubi://host:0",
            "musubi://host:65536",
            "musubi://a@host:123",
            "musubi://host:123/path",
            "musubi://host:123?query",
            "musubi://host:123#fragment",
            "musubi://::1:123",
            "musubi://[bad]:123",
        ] {
            assert!(validate_endpoint(invalid).is_err(), "{invalid}");
        }
        assert!(decode_key(&"A".repeat(1025)).is_err());
        assert!(decode_enrollment(&vec![0; MAX_EXCHANGE + 1]).is_err());
        assert!(decode_reply(&vec![0; MAX_EXCHANGE + 1]).is_err());
        for bytes in [b"".as_slice(), b"{}", b"{\"version\":1}", b"\xff", ENROLL] {
            fuzz_enrollment(bytes);
        }
        Ok(())
    }

    #[test]
    fn pathless_watcher_events_refresh_authorization() {
        let rescan = notify::Event::new(notify::EventKind::Other);
        assert!(authorization_event_relevant(&Ok(rescan)));
        let access = notify::Event::new(notify::EventKind::Access(notify::event::AccessKind::Any));
        assert!(!authorization_event_relevant(&Ok(access)));
        let unrelated =
            notify::Event::new(notify::EventKind::Modify(notify::event::ModifyKind::Any))
                .add_path(PathBuf::from("unrelated"));
        assert!(!authorization_event_relevant(&Ok(unrelated)));
    }

    #[tokio::test(start_paused = true)]
    async fn transient_accept_errors_are_retried() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let attempts = Arc::new(AtomicUsize::new(0));
        let counted = attempts.clone();
        let accepting = tokio::spawn(accept_with_retry(move || {
            let attempt = counted.fetch_add(1, Ordering::Relaxed);
            std::future::ready(match attempt {
                0 => Err(io::Error::from(io::ErrorKind::ConnectionAborted)),
                1 => Err(io::Error::other("too many open files")),
                _ => Ok("accepted"),
            })
        }));
        tokio::task::yield_now().await;
        assert_eq!(attempts.load(Ordering::Relaxed), 1);
        tokio::time::advance(Duration::from_millis(9)).await;
        assert_eq!(attempts.load(Ordering::Relaxed), 1);
        tokio::time::advance(Duration::from_millis(1)).await;
        tokio::task::yield_now().await;
        assert_eq!(attempts.load(Ordering::Relaxed), 2);
        tokio::time::advance(Duration::from_millis(19)).await;
        assert_eq!(attempts.load(Ordering::Relaxed), 2);
        tokio::time::advance(Duration::from_millis(1)).await;
        assert_eq!(accepting.await.unwrap(), "accepted");
        assert_eq!(attempts.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn invalid_secret_or_csr_does_not_consume_single_use_invitation() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Hub::open(dir.path())?;
        let (id, text) = hub.invite(true)?;
        let invitation = decode_key(&text)?;
        let key = KeyPair::generate()?;
        let csr = CertificateParams::new(Vec::<String>::new())?.serialize_request(&key)?;
        let request = |secret, csr| Enrollment {
            version: 1,
            id: id.clone(),
            secret,
            csr,
        };
        let hostile = request(random()?, vec![0]);
        let hostile = decode_enrollment(&serde_json::to_vec(&hostile)?)?;
        let err = hub.enroll(hostile).unwrap_err();
        assert_eq!(err.to_string(), "enrollment refused");
        assert!(hub.enroll(request(random()?, csr.der().to_vec())).is_err());
        assert!(
            hub.enroll(request(invitation.secret.clone(), vec![0]))
                .is_err()
        );
        // A structurally valid CSR with a forged signature must also be refused.
        let mut forged = csr.der().to_vec();
        if let Some(last) = forged.last_mut() {
            *last ^= 1;
        }
        assert!(
            hub.enroll(request(invitation.secret.clone(), forged))
                .is_err()
        );
        assert_eq!(hub.invitations()?, vec![(id.clone(), true)]);
        assert_eq!(single_use_keys(dir.path())?, vec![text.clone()]);
        assert!(hub.clients()?.is_empty());
        let certificate = hub.enroll(request(invitation.secret, csr.der().to_vec()))?;
        assert_eq!(
            hub.clients()?,
            vec![(hash(&certificate), csr_label(csr.der())?)]
        );
        let successor_keys = single_use_keys(dir.path())?;
        assert_eq!(successor_keys.len(), 1);
        let successor = successor_keys
            .first()
            .context("missing single-use successor")?;
        assert_ne!(successor, &text);
        assert!(hub.enroll(enrollment_request(&text)?).is_err());
        let mut invalid = enrollment_request(successor)?;
        invalid.secret = random()?;
        assert!(hub.enroll(invalid).is_err());
        let mut invalid = enrollment_request(successor)?;
        invalid.csr = vec![0];
        assert!(hub.enroll(invalid).is_err());
        assert_eq!(single_use_keys(dir.path())?, successor_keys);
        let _certificate = hub.enroll(enrollment_request(successor)?)?;
        assert_eq!(hub.clients()?.len(), 2);
        assert!(hub.enroll(enrollment_request(successor)?).is_err());
        let next_keys = single_use_keys(dir.path())?;
        assert_eq!(next_keys.len(), 1);
        assert_ne!(next_keys, successor_keys);
        assert!(!next_keys.contains(&text));
        Ok(())
    }

    #[test]
    fn expired_enrollment_does_not_consume_its_invitation() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Hub::open(dir.path())?;
        let (id, text) = hub.invite(true)?;
        let err = hub
            .enroll_before(enrollment_request(&text)?, tokio::time::Instant::now())
            .unwrap_err();
        assert_eq!(err.to_string(), "TLS enrollment timed out");
        assert_eq!(hub.invitations()?, vec![(id, true)]);
        assert!(hub.clients()?.is_empty());
        Ok(())
    }

    #[tokio::test]
    async fn enrollment_after_listener_start_needs_no_hub_restart() -> anyhow::Result<()> {
        let server = Server::start().await?;
        // Complete a handshake before creating the invitation, so the listener is already
        // running rather than merely spawned and waiting to be polled.
        let pin = hash(&server.hub.identity.server_cert);
        let readiness = dial(&server.address, client_config(pin, None)?).await?;
        drop(readiness);
        // A separate CLI process creates invitations through its own Hub handle. The serving
        // handle must reload the new invitation without restarting its listener.
        let manager = Hub::open(server.dir.path())?;
        let (_, invitation) = manager.invite(false)?;
        let credentials = remote_credentials(&server.address, &invitation, "alpha").await?;
        let _stream = sync_stream(&server.address, credentials).await?;
        assert!(
            !server.task.is_finished(),
            "the TLS hub stopped while enrolling"
        );
        Ok(())
    }

    #[tokio::test]
    async fn enrollment_and_mtls_relay_survive_invitation_revocation() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let (id, text) = server.hub.invite(false)?;
        let credentials = remote_credentials(&server.address, &text, "alpha").await?;
        let second = remote_credentials(&server.address, &text, "beta").await?;
        assert_ne!(hash(&credentials.certificate), hash(&second.certificate));
        assert_eq!(server.hub.clients()?.len(), 2);
        server.hub.revoke_invite(&id)?;
        assert!(
            remote_credentials(&server.address, &text, "alpha")
                .await
                .is_err()
        );
        let mut inbox = server.network.subscribe("tls.echo").await?;
        let peer = StreamTransport::connect(Arc::new(TestConnector {
            address: server.address.clone(),
            credentials,
        }))
        .await?;
        let request = peer.request(
            "tls.echo",
            Bytes::from_static(b"authenticated"),
            Duration::from_secs(2),
        );
        let answer = async {
            let message = inbox
                .next()
                .await
                .context("missing authenticated request")?;
            server
                .network
                .publish(
                    message.reply.as_deref().context("missing reply subject")?,
                    message.payload,
                )
                .await?;
            Ok::<_, anyhow::Error>(())
        };
        let (response, answered) = tokio::join!(request, answer);
        answered?;
        assert_eq!(response?, Bytes::from_static(b"authenticated"));
        let _second = sync_stream(&server.address, second).await?;
        Ok(())
    }

    #[tokio::test]
    async fn anonymous_enrollments_do_not_take_authenticated_capacity() -> anyhow::Result<()> {
        let server = Server::start_with_limits(SessionLimits {
            handshakes: 2,
            unauthenticated: 1,
            authenticated: 2,
            authentication_deadline: Duration::from_secs(2),
        })
        .await?;
        let (_, text) = server.hub.invite(false)?;
        let alpha = remote_credentials(&server.address, &text, "alpha").await?;
        let beta = remote_credentials(&server.address, &text, "beta").await?;
        let mut inbox = server.network.subscribe("tls.capacity").await?;
        let peer = StreamTransport::connect(Arc::new(TestConnector {
            address: server.address.clone(),
            credentials: alpha,
        }))
        .await?;

        let pin = hash(&server.hub.identity.server_cert);
        let mut stalled = dial(&server.address, client_config(pin.clone(), None)?).await?;
        stalled.write_all(ENROLL).await?;
        stalled.write_u32(1).await?;
        stalled.flush().await?;
        tokio::task::yield_now().await;

        let mut refused = dial(&server.address, client_config(pin, None)?).await?;
        refused.write_all(ENROLL).await?;
        refused.write_u32(1).await?;
        refused.flush().await?;
        let mut byte = [0; 1];
        let read = timeout(Duration::from_secs(2), refused.read(&mut byte)).await?;
        assert!(
            read.is_err() || read? == 0,
            "second anonymous peer stayed open"
        );

        let _beta_stream = sync_stream(&server.address, beta).await?;
        let request = peer.request(
            "tls.capacity",
            Bytes::from_static(b"authenticated"),
            Duration::from_secs(2),
        );
        let answer = async {
            let message = inbox
                .next()
                .await
                .context("missing authenticated request")?;
            server
                .network
                .publish(
                    message.reply.as_deref().context("missing reply subject")?,
                    message.payload,
                )
                .await?;
            Ok::<_, anyhow::Error>(())
        };
        let (response, answered) = tokio::join!(request, answer);
        answered?;
        assert_eq!(response?, Bytes::from_static(b"authenticated"));
        Ok(())
    }

    #[tokio::test]
    async fn authentication_uses_one_overall_deadline() -> anyhow::Result<()> {
        let server = Server::start_with_limits(SessionLimits {
            handshakes: 1,
            unauthenticated: 1,
            authenticated: 1,
            authentication_deadline: Duration::from_secs(1),
        })
        .await?;
        let (_, text) = server.hub.invite(false)?;
        let credentials = remote_credentials(&server.address, &text, "alpha").await?;
        let (host, address) = endpoint(&server.address)?;
        let socket = TcpStream::connect(address).await?;
        tokio::time::sleep(Duration::from_millis(750)).await;
        let pin = hash(&server.hub.identity.server_cert);
        let mut stalled = TlsConnector::from(Arc::new(client_config(pin, None)?))
            .connect(ServerName::try_from(host)?, socket)
            .await?;
        stalled.write_all(ENROLL).await?;
        stalled.write_u32(1).await?;
        stalled.flush().await?;
        tokio::time::sleep(Duration::from_millis(300)).await;
        let mut byte = [0; 1];
        let read = timeout(Duration::from_millis(100), stalled.read(&mut byte)).await;
        assert!(
            matches!(read, Ok(Ok(0) | Err(_))),
            "authentication deadline restarted"
        );
        let _stream = sync_stream(&server.address, credentials).await?;
        Ok(())
    }

    #[tokio::test]
    async fn anonymous_sync_and_unlisted_certificates_are_refused() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let pin = hash(&server.hub.identity.server_cert);
        let mut anonymous = dial(&server.address, client_config(pin.clone(), None)?).await?;
        anonymous.write_all(SYNC).await?;
        let mut first = [0; 1];
        let read = timeout(Duration::from_secs(2), anonymous.read(&mut first)).await?;
        assert!(
            read.is_err() || read? == 0,
            "anonymous peer received sync bytes"
        );
        let key = KeyPair::generate()?;
        let csr = CertificateParams::new(Vec::<String>::new())?.serialize_request(&key)?;
        let credentials = Credentials {
            pin,
            certificate: server.hub.identity.issue(csr.der())?.0,
            private_key: key.serialize_der(),
        };
        assert!(sync_stream(&server.address, credentials).await.is_err());
        assert!(server.hub.clients()?.is_empty());
        Ok(())
    }

    #[tokio::test]
    async fn pinned_identity_is_checked_before_secret_disclosure() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let (_, text) = server.hub.invite(false)?;
        let mut key = decode_key(&text)?;
        key.pin = random()?;
        let wrong_pin = encode_key(&key)?;
        assert!(
            remote_credentials(&server.address, &wrong_pin, "alpha")
                .await
                .is_err()
        );
        assert!(server.hub.clients()?.is_empty());
        assert_eq!(server.hub.invitations()?.len(), 1);
        Ok(())
    }

    #[derive(Debug)]
    struct ForgedResolver(Arc<rustls::sign::CertifiedKey>);

    impl rustls::server::ResolvesServerCert for ForgedResolver {
        fn resolve(
            &self,
            _hello: rustls::server::ClientHello<'_>,
        ) -> Option<Arc<rustls::sign::CertifiedKey>> {
            Some(self.0.clone())
        }
    }

    #[tokio::test]
    async fn pinned_certificate_still_requires_a_valid_handshake_signature() -> anyhow::Result<()> {
        let identity = Identity::generate()?;
        let attacker = KeyPair::generate()?;
        let signing_key = rustls::crypto::ring::sign::any_supported_type(&PrivateKeyDer::Pkcs8(
            PrivatePkcs8KeyDer::from(attacker.serialize_der()),
        ))?;
        let resolver = ForgedResolver(Arc::new(rustls::sign::CertifiedKey::new(
            vec![CertificateDer::from(identity.server_cert.clone())],
            signing_key,
        )));
        let config = rustls::ServerConfig::builder_with_provider(Arc::new(
            rustls::crypto::ring::default_provider(),
        ))
        .with_safe_default_protocol_versions()?
        .with_no_client_auth()
        .with_cert_resolver(Arc::new(resolver));
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = format!("musubi://{}", listener.local_addr()?);
        let secret = random()?;
        let invitation = InvitationKey {
            version: 1,
            id: invitation_id(&secret)?,
            secret,
            pin: hash(&identity.server_cert),
        };
        let text = encode_key(&invitation)?;
        let attacker_task = async {
            let (socket, _) = listener.accept().await?;
            let result = TlsAcceptor::from(Arc::new(config)).accept(socket).await;
            ensure!(result.is_err(), "forged signature admitted plaintext");
            Ok::<_, anyhow::Error>(())
        };
        let client = remote_credentials(&address, &text, "alpha");
        let (attacker_result, client_result) = timeout(Duration::from_secs(2), async {
            tokio::join!(attacker_task, client)
        })
        .await?;
        attacker_result?;
        assert!(client_result.is_err());
        Ok(())
    }

    #[tokio::test]
    async fn single_use_invitation_admits_exactly_one_concurrent_enrollment() -> anyhow::Result<()>
    {
        let server = Server::start().await?;
        let (_, text) = server.hub.invite(true)?;
        let (a, b) = tokio::join!(
            remote_credentials(&server.address, &text, "alpha"),
            remote_credentials(&server.address, &text, "beta"),
        );
        assert_eq!(usize::from(a.is_ok()) + usize::from(b.is_ok()), 1);
        let ((Ok(first), Err(_)) | (Err(_), Ok(first))) = (a, b) else {
            return Err(anyhow::anyhow!(
                "single-use enrollment did not have exactly one winner"
            ));
        };
        assert_eq!(server.hub.clients()?.len(), 1);
        let successors = single_use_keys(server.dir.path())?;
        assert_eq!(successors.len(), 1);
        let successor = successors.first().context("missing single-use successor")?;
        assert_ne!(successor, &text);
        assert!(
            remote_credentials(&server.address, &text, "rejected")
                .await
                .is_err()
        );
        assert_eq!(single_use_keys(server.dir.path())?, successors);
        let second = remote_credentials(&server.address, successor, "next-client").await?;
        assert_eq!(server.hub.clients()?.len(), 2);
        assert!(
            remote_credentials(&server.address, successor, "rejected")
                .await
                .is_err()
        );
        let current = single_use_keys(server.dir.path())?;
        assert_eq!(current.len(), 1);
        assert_ne!(current, successors);
        assert!(!current.contains(&text));
        let _first_stream = sync_stream(&server.address, first).await?;
        let _second_stream = sync_stream(&server.address, second).await?;
        Ok(())
    }

    #[test]
    fn independent_hub_handles_serialize_single_use_enrollment() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let a = Hub::open(dir.path())?;
        let b = Hub::open(dir.path())?;
        let (_, text) = a.invite(true)?;
        let invitation = decode_key(&text)?;
        let request = || -> anyhow::Result<Enrollment> {
            let key = KeyPair::generate()?;
            let csr = CertificateParams::new(Vec::<String>::new())?.serialize_request(&key)?;
            Ok(Enrollment {
                version: 1,
                id: invitation.id.clone(),
                secret: invitation.secret.clone(),
                csr: csr.der().to_vec(),
            })
        };
        let (ra, rb) = (request()?, request()?);
        let barrier = std::sync::Barrier::new(2);
        let count = std::thread::scope(|scope| -> anyhow::Result<usize> {
            let ta = scope.spawn(|| {
                barrier.wait();
                a.enroll(ra).is_ok()
            });
            let tb = scope.spawn(|| {
                barrier.wait();
                b.enroll(rb).is_ok()
            });
            let aa = ta
                .join()
                .map_err(|_| anyhow::anyhow!("first enrollment panicked"))?;
            let bb = tb
                .join()
                .map_err(|_| anyhow::anyhow!("second enrollment panicked"))?;
            Ok(usize::from(aa) + usize::from(bb))
        })?;
        assert_eq!(count, 1);
        assert_eq!(a.clients()?.len(), 1);
        assert_eq!(b.clients()?.len(), 1);
        assert!(a.enroll(enrollment_request(&text)?).is_err());
        assert!(b.enroll(enrollment_request(&text)?).is_err());
        let successors = single_use_keys(dir.path())?;
        assert_eq!(successors.len(), 1);
        let successor = successors.first().context("missing single-use successor")?;
        let _certificate = b.enroll(enrollment_request(successor)?)?;
        assert_eq!(a.clients()?.len(), 2);
        assert_eq!(b.clients()?.len(), 2);
        assert!(a.enroll(enrollment_request(successor)?).is_err());
        let current = single_use_keys(dir.path())?;
        assert_eq!(current.len(), 1);
        assert_ne!(current, successors);
        assert!(!current.contains(&text));
        assert_eq!(a.invitations()?, b.invitations()?);
        Ok(())
    }

    #[test]
    fn single_use_key_lookup_is_private_local_and_read_only() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let absent = dir.path().join("absent-hub");
        assert!(single_use_keys(&absent)?.is_empty());
        assert!(!absent.exists(), "key lookup initialized a missing hub");
        let hub = Hub::open(dir.path())?;
        let (_, reusable) = hub.invite(false)?;
        let (id, rotating) = hub.invite(true)?;
        let reusable_secret = decode_key(&reusable)?.secret;
        let rotating_secret = decode_key(&rotating)?.secret;
        let path = hub.dir.join("authorization.json");
        let authorization = fs::read_to_string(&path)?;
        assert!(!authorization.contains(&reusable_secret));
        assert!(authorization.contains(&rotating_secret));
        let authorization_mtime = fs::metadata(&path)?.modified()?;
        let identity_path = hub.dir.join("identity.json");
        let identity = fs::read(&identity_path)?;
        let identity_mtime = fs::metadata(&identity_path)?.modified()?;
        assert_eq!(single_use_keys(dir.path())?, vec![rotating]);
        assert_eq!(fs::read_to_string(&path)?, authorization);
        assert_eq!(fs::metadata(&path)?.modified()?, authorization_mtime);
        assert_eq!(fs::read(&identity_path)?, identity);
        assert_eq!(fs::metadata(&identity_path)?.modified()?, identity_mtime);
        hub.revoke_invite(&id)?;
        assert!(single_use_keys(dir.path())?.is_empty());
        let _certificate = hub.enroll(enrollment_request(&reusable)?)?;
        assert!(single_use_keys(dir.path())?.is_empty());
        Ok(())
    }

    #[test]
    fn invalid_invitation_state_is_rejected_without_rewriting_it() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Hub::open(dir.path())?;
        let (id, key) = hub.invite(true)?;
        let path = hub.dir.join("authorization.json");
        let valid = fs::read(&path)?;
        let original: serde_json::Value = serde_json::from_slice(&valid)?;
        for case in [
            "missing",
            "invalid",
            "mismatched",
            "hash",
            "verifier",
            "id",
            "unknown",
            "reusable",
        ] {
            let mut state = original.clone();
            let invite = &mut state["invitations"][id.as_str()];
            match case {
                "missing" => {
                    invite.as_object_mut().unwrap().remove("secret");
                }
                "invalid" => invite["secret"] = "invalid".into(),
                "mismatched" => invite["secret"] = random()?.into(),
                "hash" => invite["secret_hash"] = "invalid".into(),
                "verifier" => invite["secret_hash"] = secret_tag(&random()?).into(),
                "id" => {
                    let entry = state["invitations"]
                        .as_object_mut()
                        .unwrap()
                        .remove(&id)
                        .unwrap();
                    state["invitations"][random()?] = entry;
                }
                "unknown" => invite["unsupported"] = true.into(),
                "reusable" => invite["single_use"] = false.into(),
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec(&state)?;
            crate::config::write_private(&path, &bytes)?;
            let mtime = fs::metadata(&path)?.modified()?;
            assert!(Hub::open(dir.path()).is_err(), "{case}");
            assert!(single_use_keys(dir.path()).is_err(), "{case}");
            assert!(hub.enroll(enrollment_request(&key)?).is_err(), "{case}");
            assert_eq!(fs::read(&path)?, bytes, "{case}");
            assert_eq!(fs::metadata(&path)?.modified()?, mtime, "{case}");
        }
        crate::config::write_private(&path, &valid)?;
        assert_eq!(single_use_keys(dir.path())?, vec![key]);
        let _reusable = hub.invite(false)?;
        Ok(())
    }

    #[tokio::test(flavor = "current_thread")]
    async fn authorization_reload_does_not_block_the_async_runtime() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Arc::new(Hub::open(dir.path())?);
        let lock_path = hub.dir.join("state.lock");
        let (locked, waiting) = std::sync::mpsc::channel();
        let holder = std::thread::spawn(move || {
            let _lock = crate::lock::lock(&lock_path).unwrap();
            locked.send(()).unwrap();
            std::thread::sleep(Duration::from_millis(250));
        });
        waiting.recv()?;
        let started = std::time::Instant::now();
        let reloading = tokio::spawn({
            let hub = hub.clone();
            async move { hub.reload_authorization().await }
        });
        tokio::task::yield_now().await;
        assert!(
            started.elapsed() < Duration::from_millis(100),
            "authorization reload blocked the async runtime for {:?}",
            started.elapsed()
        );
        holder.join().unwrap();
        reloading.await??;
        Ok(())
    }

    #[test]
    fn authorization_refresh_does_not_trust_an_unchanged_timestamp() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Hub::open(dir.path())?;
        let (_, text) = hub.invite(false)?;
        let invitation = decode_key(&text)?;
        let key = KeyPair::generate()?;
        let csr = CertificateParams::new(Vec::<String>::new())?.serialize_request(&key)?;
        let certificate = hub.enroll(Enrollment {
            version: 1,
            id: invitation.id,
            secret: invitation.secret,
            csr: csr.der().to_vec(),
        })?;
        let id = hash(&certificate);
        let path = hub.dir.join("authorization.json");
        let previous_mtime = fs::metadata(&path)?.modified()?;
        let manager = Hub::open(dir.path())?;
        manager.revoke_client(&id)?;
        fs::OpenOptions::new()
            .write(true)
            .open(&path)?
            .set_times(fs::FileTimes::new().set_modified(previous_mtime))?;
        assert_eq!(fs::metadata(&path)?.modified()?, previous_mtime);
        assert!(
            hub.authorized(&id),
            "the independent handle must still have its old cache"
        );
        // The notification and periodic paths both use this unconditional reload.
        hub.refresh()?;
        assert!(!hub.authorized(&id));
        assert!(hub.clients()?.is_empty());
        Ok(())
    }

    #[test]
    fn hostile_csr_labels_are_bounded_and_safely_persisted() -> anyhow::Result<()> {
        let dir = musubi_testutil::tempdir();
        let hub = Hub::open(dir.path())?;
        let (id, text) = hub.invite(true)?;
        let invitation = decode_key(&text)?;
        let request = |label: &str| -> anyhow::Result<Enrollment> {
            let key = KeyPair::generate()?;
            let mut params = CertificateParams::new(Vec::<String>::new())?;
            params.distinguished_name = rcgen::DistinguishedName::new();
            params
                .distinguished_name
                .push(rcgen::DnType::CommonName, label);
            let csr = params.serialize_request(&key)?;
            Ok(Enrollment {
                version: 1,
                id: id.clone(),
                secret: invitation.secret.clone(),
                csr: csr.der().to_vec(),
            })
        };
        assert!(hub.enroll(request("")?).is_err());
        assert!(hub.enroll(request(&"x".repeat(256))?).is_err());
        assert_eq!(hub.invitations()?, vec![(id.clone(), true)]);
        let certificate = hub.enroll(request(" beta\x1b[2J\r\n\u{202e} ")?)?;
        let clients = Hub::open(dir.path())?.clients()?;
        assert_eq!(
            clients,
            vec![(hash(&certificate), "beta?[2J???".to_owned())]
        );
        let successors = single_use_keys(dir.path())?;
        assert_eq!(successors.len(), 1);
        let successor = successors.first().context("missing single-use successor")?;
        let _certificate = hub.enroll(enrollment_request(successor)?)?;
        assert!(hub.enroll(enrollment_request(successor)?).is_err());
        let current = single_use_keys(dir.path())?;
        assert_eq!(current.len(), 1);
        assert_ne!(current, successors);
        assert!(!current.contains(&text));
        Ok(())
    }

    #[tokio::test]
    async fn labels_select_only_the_revoked_certificate() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let (_, text) = server.hub.invite(false)?;
        let alpha = remote_credentials(&server.address, &text, "alpha").await?;
        let alpha_id = hash(&alpha.certificate);
        let beta = remote_credentials(&server.address, &text, "beta").await?;
        let manager = Hub::open(server.dir.path())?;
        let clients = manager.clients()?;
        assert_eq!(clients.len(), 2);
        let (id, _) = clients
            .iter()
            .find(|(_, label)| label == "beta")
            .context("beta's descriptive label was not persisted")?;
        assert_eq!(id, &hash(&beta.certificate));
        let _beta_stream = sync_stream(&server.address, beta.clone()).await?;
        manager.revoke_client(id)?;
        assert!(sync_stream(&server.address, beta).await.is_err());
        let _alpha_stream = sync_stream(&server.address, alpha).await?;
        assert_eq!(manager.clients()?, vec![(alpha_id, "alpha".to_owned())]);
        Ok(())
    }

    #[tokio::test]
    async fn duplicate_labels_do_not_merge_client_authorizations() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let (_, text) = server.hub.invite(false)?;
        let a = remote_credentials(&server.address, &text, "same-hostname").await?;
        let b = remote_credentials(&server.address, &text, "same-hostname").await?;
        assert_ne!(hash(&a.certificate), hash(&b.certificate));
        let clients = server.hub.clients()?;
        assert_eq!(clients.len(), 2);
        assert!(clients.iter().all(|(_, label)| label == "same-hostname"));
        server.hub.revoke_client(&hash(&a.certificate))?;
        assert!(sync_stream(&server.address, a).await.is_err());
        let _surviving_stream = sync_stream(&server.address, b).await?;
        Ok(())
    }

    #[tokio::test]
    async fn revocation_closes_existing_stream_and_refuses_reconnect() -> anyhow::Result<()> {
        let server = Server::start().await?;
        let (_, text) = server.hub.invite(false)?;
        let credentials = remote_credentials(&server.address, &text, "alpha").await?;
        let mut stream = sync_stream(&server.address, credentials.clone()).await?;
        // A separate CLI process has its own Hub handle, not the serving instance's watcher.
        let manager = Hub::open(server.dir.path())?;
        manager.revoke_client(&hash(&credentials.certificate))?;
        let mut byte = [0; 1];
        let result = timeout(Duration::from_secs(2), stream.read(&mut byte)).await?;
        assert!(
            result.is_err() || result? == 0,
            "revoked stream stayed open"
        );
        assert!(sync_stream(&server.address, credentials).await.is_err());
        assert_eq!(server.hub.invitations()?.len(), 1);
        let renewed = remote_credentials(&server.address, &text, "alpha").await?;
        let _stream = sync_stream(&server.address, renewed).await?;
        Ok(())
    }
}
