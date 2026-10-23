//! Bundles (`musubi_jj::objects::bundle`): reading never panics, and the records of one
//! that reads, written to a bundle of their own, read back the same.

#![no_main]

use std::collections::HashMap;
use std::fs;
use std::io::Read as _;
use std::path::Path;

use libfuzzer_sys::fuzz_target;
use musubi_fuzz::scratch;
use musubi_jj::objects::ObjectError;
use musubi_jj::objects::bundle;
use musubi_jj::objects::bundle::BundleWriter;
use musubi_jj::objects::bundle::ObjectKind;
use musubi_jj::objects::bundle::Record;

const MAGIC: &[u8] = b"MUSUBI-BUNDLE 2\n";

/// A record as read, comparable: a pack's bytes rather than where they are, and a view
/// delta as the view it makes of its base.
#[derive(Debug, PartialEq)]
enum Seen {
    Extras(Vec<u8>, Vec<u8>),
    Pack(Vec<u8>),
    Object(ObjectKind, Vec<u8>, Vec<u8>),
    View(Vec<u8>, Vec<u8>),
    ViewDelta(Vec<u8>, Vec<u8>, Vec<u8>),
    Operation(Vec<u8>, Vec<u8>),
}

fuzz_target!(|data: &[u8]| {
    let Some((&choice, rest)) = data.split_first() else {
        return;
    };
    // Most inputs get the header, which the fuzzer would otherwise have to find first.
    let bytes = if choice & 1 == 0 {
        [MAGIC, rest].concat()
    } else {
        rest.to_vec()
    };
    let path = scratch().join("bundle");
    fs::write(&path, &bytes).unwrap();
    let Some(records) = read(&path) else {
        return;
    };
    let copy = scratch().join("copy");
    write(&copy, &records, choice & 2 != 0);
    assert_eq!(read(&copy).as_ref(), Some(&records));
});

/// The records of the bundle at `path`, if it reads and its view deltas apply, each to a
/// view before it in the bundle or, if none is, to an empty one.
fn read(path: &Path) -> Option<Vec<Seen>> {
    let mut records = vec![];
    let mut views: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();
    let mut applies = true;
    bundle::read(path, |record| {
        records.push(match record {
            Record::Extras { commit, value } => Seen::Extras(commit, value),
            Record::Pack(pack) => {
                let mut bytes = vec![];
                pack.reader()?.read_to_end(&mut bytes)?;
                assert_eq!(bytes.len() as u64, pack.len());
                Seen::Pack(bytes)
            }
            Record::Object { kind, id, contents } => Seen::Object(kind, id, contents),
            Record::View { id, contents } => {
                views.insert(id.clone(), contents.clone());
                Seen::View(id, contents)
            }
            Record::ViewDelta { id, base, delta } => {
                let base_view = views.get(&base).map_or(&[][..], Vec::as_slice);
                match bundle::apply_view_delta(base_view, &delta) {
                    Ok(view) => {
                        views.insert(id.clone(), view.clone());
                        Seen::ViewDelta(id, base, view)
                    }
                    Err(_) => {
                        applies = false;
                        return Ok(());
                    }
                }
            }
            Record::Operation { id, contents } => Seen::Operation(id, contents),
        });
        Ok::<_, ObjectError>(())
    })
    .ok()?;
    applies.then_some(records)
}

/// Writes `records` as a bundle at `path`, all but packs compressed if `compress`.
fn write(path: &Path, records: &[Seen], compress: bool) {
    let mut writer = BundleWriter::create(path).unwrap();
    let mut compressing = false;
    let mut views: HashMap<&[u8], &[u8]> = HashMap::new();
    for record in records {
        if compress && !compressing && !matches!(record, Seen::Pack(_)) {
            writer.begin_compressed().unwrap();
            compressing = true;
        }
        match record {
            Seen::Extras(commit, value) => writer.extras(commit, value),
            Seen::Pack(bytes) => {
                compressing = false;
                writer.pack_from(|out| Ok(out.write_all(bytes)?))
            }
            Seen::Object(kind, id, contents) => writer.object(*kind, id, contents),
            Seen::View(id, contents) => {
                views.insert(id, contents);
                writer.view(id, contents)
            }
            Seen::ViewDelta(id, base, view) => {
                let base_view = views.get(base.as_slice()).copied().unwrap_or_default();
                views.insert(id, view);
                writer.view_delta(id, base, base_view, view)
            }
            Seen::Operation(id, contents) => writer.operation(id, contents),
        }
        .unwrap();
    }
    writer.finish().unwrap();
}
