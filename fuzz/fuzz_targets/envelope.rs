//! Messages (`musubi_sync::wire`): decoding never panics; what decodes encodes to a message
//! that decodes the same; and nothing may follow one. postcard takes varints longer than
//! they need be, so a message may have more than one encoding.

#![no_main]

use std::fmt::Debug;

use libfuzzer_sys::fuzz_target;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HeadNotice;
use musubi_sync::wire::HubReply;
use musubi_sync::wire::HubRequest;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use serde::Deserialize;
use serde::Serialize;

fuzz_target!(|data: &[u8]| {
    let Some((&choice, rest)) = data.split_first() else {
        return;
    };
    if choice & 0x40 != 0 {
        let identity = String::from_utf8_lossy(rest).into_owned();
        let backend = match choice & 0x3 {
            0 => musubi_jj::objects::Backend::GIT,
            1 => musubi_jj::objects::Backend::Git(musubi_jj::objects::GitHash::Sha256),
            _ => musubi_jj::objects::Backend::Simple,
        };
        let request = musubi_hub::hub_dir::JoinRequest {
            choice: musubi_hub::hub_dir::JoinChoice::Match,
            backend,
            clone_config: [("user.name".to_owned(), identity.clone())].into(),
            remotes: vec![("origin".to_owned(), identity.clone())],
            remote_bindings: [(
                format!("origin.{identity}"),
                musubi_jj::remote_url::RemoteBinding {
                    fetch: Some(identity.clone()),
                    push: [identity].into(),
                },
            )]
            .into(),
            dir_name: "repo".to_owned(),
            roots: vec![],
            remote_targets: vec![],
            machine: "alpha#aaaa".to_owned(),
        };
        let snapshot = musubi_jj::remote_url::JoinRemotes {
            urls: Default::default(),
            bindings: request.remote_bindings.clone(),
        };
        assert_eq!(
            musubi_jj::remote_url::JoinRemotes::recorded_bindings(&snapshot.attributes("hive")),
            snapshot.bindings
        );
        round_trip::<HubWideRequest>(
            &Envelope::encode(HubWideRequest::PrepareClone {
                hive: "hive".to_owned().into(),
                backend: request.backend,
                remote_bindings: request.remote_bindings.clone(),
            })
            .unwrap(),
        );
        round_trip::<HubWideRequest>(&Envelope::encode(HubWideRequest::Join(request)).unwrap());
    }
    // Most inputs get this release's versions in front, which the fuzzer would otherwise
    // have to find before it reached any body.
    let bytes = if choice & 0x80 == 0 {
        [Envelope::encode(()).unwrap(), rest.to_vec()].concat()
    } else {
        rest.to_vec()
    };
    match (choice & 0x7f) % 5 {
        0 => round_trip::<HubRequest>(&bytes),
        1 => round_trip::<HubReply>(&bytes),
        2 => round_trip::<HubWideRequest>(&bytes),
        3 => round_trip::<HubWideReply>(&bytes),
        _ => round_trip::<HeadNotice>(&bytes),
    }
});

fn round_trip<T>(bytes: &[u8])
where
    T: Clone + Debug + PartialEq + Serialize + for<'de> Deserialize<'de>,
{
    if let Ok(body) = Envelope::<T>::decode(bytes) {
        let mut encoded = Envelope::encode(body.clone()).unwrap();
        assert_eq!(Envelope::<T>::decode(&encoded).unwrap(), body);
        encoded.push(0);
        assert!(Envelope::<T>::decode(&encoded).is_err());
    }
}
