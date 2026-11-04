//! Persisting record state, local renaming steps, and hub renamings.

use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use serde::Deserialize;
use serde::Serialize;

use super::Earlier;
use super::NodeError;
use super::NodeRepo;
use super::Realign;
use super::Records;
use super::digests;
use super::fixup::Fixup;

use crate::files;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::records::HubOp;
use crate::records::Record;
use crate::records::RecordDigest;
use crate::records::RecordPrefix;
use crate::translation_map::ID_HEX_LEN;
use crate::translation_map::whole_id;

const HUB_RENAMINGS_FILE: &str = "hub-renamings";
const STEPS_FILE: &str = "superseded";
const RECORDS_FILE: &str = "records.json";
/// [`Realign`] as `records.json` has it, in hex.
#[derive(Serialize, Deserialize)]
struct RealignFile {
    from: Vec<(String, Vec<String>)>,
    to: Vec<String>,
    canonical: Vec<(String, String)>,
}

impl Realign {
    fn to_file(&self) -> RealignFile {
        let hex = |ops: &[LocalOp]| ops.iter().map(|op| op.0.hex()).collect::<Vec<_>>();
        let mut from: Vec<(String, Vec<String>)> = self
            .from
            .iter()
            .map(|(old, new)| (old.0.hex(), hex(new)))
            .collect();
        from.sort();
        let mut canonical: Vec<(String, String)> = self
            .canonical
            .iter()
            .map(|(local, canonical)| (local.0.hex(), canonical.0.hex()))
            .collect();
        canonical.sort();
        RealignFile {
            from,
            to: hex(&self.to),
            canonical,
        }
    }

    fn from_file(path: &Path, file: &RealignFile) -> Result<Self, NodeError> {
        let ops = |hexes: &[String]| -> Result<Vec<LocalOp>, NodeError> {
            Ok(parse_ids(path, hexes)?.into_iter().map(LocalOp).collect())
        };
        let mut from = HashMap::new();
        for (old, new) in &file.from {
            from.insert(ops(std::slice::from_ref(old))?.swap_remove(0), ops(new)?);
        }
        let mut canonical = HashMap::new();
        for (local, op) in &file.canonical {
            let [local, op] = [local, op].map(|hex| parse_ids(path, std::slice::from_ref(hex)));
            canonical.insert(
                LocalOp(local?.swap_remove(0)),
                CanonicalOp(op?.swap_remove(0)),
            );
        }
        Ok(Self {
            from,
            to: ops(&file.to)?,
            canonical,
        })
    }
}

#[derive(Default, Serialize, Deserialize)]
struct RecordsFile {
    /// The count and hex digest of `Records::prefix`, if it has any.
    #[serde(default)]
    prefix: Option<(u64, String)>,
    applied: Vec<Vec<String>>,
    pending: Vec<String>,
    fixup: Option<Fixup>,
    fixup_written: bool,
    #[serde(default)]
    fixup_from: Option<String>,
    #[serde(default)]
    moving: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    realign: Option<RealignFile>,
    /// How many renamings of the steps log count: one appended after is from a run cut short.
    #[serde(default)]
    steps: usize,
    #[serde(default)]
    fresh: bool,
    /// `Records::earlier`, each the hex digest of the records before it, and the record.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    earlier: Vec<(String, Vec<String>)>,
    /// `Records::custody`, as `earlier` is.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    custody: Vec<(String, Vec<String>)>,
}

fn hex_ids(record: &Record) -> Vec<String> {
    record.ops().iter().map(|op| op.0.0.hex()).collect()
}

fn parse_record(path: &Path, hexes: &[String]) -> Result<Record, NodeError> {
    Ok(Record::new(
        parse_ids(path, hexes)?
            .into_iter()
            .map(|op| HubOp(CanonicalOp(op))),
    ))
}

fn parse_ids(path: &Path, hexes: &[String]) -> Result<Vec<OperationId>, NodeError> {
    hexes
        .iter()
        .map(|hex| {
            OperationId::try_from_hex(hex).ok_or_else(|| NodeError::Io {
                path: path.to_owned(),
                source: std::io::Error::other(format!("bad operation id {hex}")),
            })
        })
        .collect()
}

/// A digest in hex, as the renamings log names records by.
pub(super) fn digest_hex(digest: &RecordDigest) -> String {
    jj_lib::hex_util::encode_hex(digest.bytes())
}

/// Reads a file musubi appends to, or nothing if there is none.
fn read_log(path: &Path) -> Result<String, NodeError> {
    match fs::read(path) {
        Ok(bytes) => Ok(String::from_utf8_lossy(&bytes).into_owned()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(String::new()),
        Err(source) => Err(NodeError::Io {
            path: path.to_owned(),
            source,
        }),
    }
}

/// Appends `text` to the file at `path`, in one write.
fn append_log(path: &Path, text: &str) -> Result<(), NodeError> {
    let io = |source| NodeError::Io {
        path: path.to_owned(),
        source,
    };
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .map_err(io)?;
    file.write_all(text.as_bytes()).map_err(io)
}

/// The width of the numbers in a log's headers, so that a header torn in one names nothing.
const NUMBER_DIGITS: usize = 20;

/// A number in a log's header, whole.
fn whole_number(digits: &str) -> Option<usize> {
    (digits.len() == NUMBER_DIGITS && digits.bytes().all(|b| b.is_ascii_digit()))
        .then(|| digits.parse().ok())
        .flatten()
}

/// A block of a log as read: what its whole lines say, how many lines its header counts, and
/// how many it has.
#[derive(Debug, Default)]
pub(super) struct Block<T> {
    read: T,
    count: usize,
    seen: usize,
}

impl<T> Block<T> {
    fn new(read: T, count: usize) -> Self {
        Self {
            read,
            count,
            seen: 0,
        }
    }

    /// What it says, if it has every line its header counts: a power cut can lose an append
    /// after the write that counts on it, or part of one.
    pub(super) fn whole(self) -> Option<T> {
        (self.seen == self.count).then_some(self.read)
    }
}

/// How the records after the first `from` of `records`, which come after the records `start`
/// is the digest of, renamed the hub's history, as the renamings log has them: each a `record
/// <digest> <lines>` line, the digest being of the records up to it, then a `new old` line for
/// each operation. It starts a line, so that it stands apart from a line a crash tore before
/// it.
pub(super) fn format_hub_renamings(
    start: &RecordDigest,
    records: &[Record],
    from: usize,
    renamings: &[HashMap<CanonicalOp, CanonicalOp>],
) -> String {
    let digests = digests(start, records);
    let mut text = String::from("\n");
    for (k, renaming) in renamings.iter().enumerate() {
        let digest = digest_hex(&digests[from + k + 1]);
        let lines = renaming.len();
        writeln!(text, "record {digest} {lines:0NUMBER_DIGITS$}").expect("writing to a String");
        for (new, old) in renaming {
            writeln!(text, "{} {}", new.0.hex(), old.0.hex()).expect("writing to a String");
        }
    }
    text
}

/// Reads the renamings log ([`format_hub_renamings`]), by digest: a block counts only with the
/// records it was written for, and the last block of a digest counts. Every line has one
/// length, so one torn anywhere, as a crash leaves the end of an append, names nothing.
pub(super) fn parse_hub_renamings(
    text: &str,
) -> HashMap<String, Block<HashMap<CanonicalOp, CanonicalOp>>> {
    let mut renamings = HashMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        if let Some(header) = line.strip_prefix("record ") {
            if let Some((digest, lines)) = header.split_once(' ')
                && digest.len() == ID_HEX_LEN
                && digest.bytes().all(|b| b.is_ascii_hexdigit())
                && let Some(lines) = whole_number(lines)
            {
                current = Some(digest.to_owned());
                renamings.insert(digest.to_owned(), Block::new(HashMap::new(), lines));
            }
            continue;
        }
        let block = current
            .as_ref()
            .and_then(|digest| renamings.get_mut(digest));
        if let (Some(block), Some((new, old))) = (block, line.split_once(' '))
            && let (Some(new), Some(old)) = (whole_id(new), whole_id(old))
        {
            block.read.insert(CanonicalOp(new), CanonicalOp(old));
            block.seen += 1;
        }
    }
    renamings
}

/// A renaming, and what it dropped.
pub(super) type Step = (
    HashMap<CanonicalOp, Vec<CanonicalOp>>,
    Vec<CanonicalOp>,
    HashMap<LocalOp, CanonicalOp>,
);

/// Renaming `number`, which dropped `dropped`, as the steps log has it: a `step <number>
/// <lines>` line, then an `old new` line for each operation it superseded and each it became,
/// in order, or `old -` where it became none; a dropped operation's lines start with `-`. It
/// starts a line, so that it stands apart from a line a crash tore before it.
pub(super) fn format_step(
    number: usize,
    step: &HashMap<CanonicalOp, Vec<CanonicalOp>>,
    dropped: &HashSet<CanonicalOp>,
    sources: &HashMap<LocalOp, CanonicalOp>,
) -> String {
    let lines: usize = step.values().map(|new| new.len().max(1)).sum::<usize>() + sources.len();
    let mut text = format!("\nstep {number:0NUMBER_DIGITS$} {lines:0NUMBER_DIGITS$}\n");
    for (old, new) in step {
        let mark = if dropped.contains(old) { "-" } else { "" };
        if new.is_empty() {
            writeln!(text, "{mark}{} -", old.0.hex()).expect("writing to a String");
        }
        for op in new {
            writeln!(text, "{mark}{} {}", old.0.hex(), op.0.hex()).expect("writing to a String");
        }
    }
    for (local, canonical) in sources {
        writeln!(text, "source {} {}", local.0.hex(), canonical.0.hex())
            .expect("writing to a String");
    }
    text
}

/// Reads the steps log ([`format_step`]), by number, the last block of a number counting.
/// Every line has one length, so one torn anywhere, as a crash leaves the end of an append,
/// names nothing.
pub(super) fn parse_steps(text: &str) -> std::collections::BTreeMap<usize, Block<Step>> {
    let mut steps = std::collections::BTreeMap::new();
    let mut current = None;
    for line in text.lines() {
        if let Some(header) = line.strip_prefix("step ") {
            if let Some((number, lines)) = header.split_once(' ')
                && let (Some(number), Some(lines)) = (whole_number(number), whole_number(lines))
            {
                current = Some(number);
                steps.insert(number, Block::new(Step::default(), lines));
            }
            continue;
        }
        if let Some(pair) = line.strip_prefix("source ") {
            if let Some((local, canonical)) = pair.split_once(' ')
                && let (Some(local), Some(canonical)) = (whole_id(local), whole_id(canonical))
                && let Some(block) = current.and_then(|number| steps.get_mut(&number))
            {
                block.read.2.insert(LocalOp(local), CanonicalOp(canonical));
                block.seen += 1;
            }
            continue;
        }
        let (dropped, line) = match line.strip_prefix('-') {
            Some(line) => (true, line),
            None => (false, line),
        };
        let Some((old, new)) = line.split_once(' ') else {
            continue;
        };
        let new = match new {
            "-" => Some(None),
            hex => whole_id(hex).map(|op| Some(CanonicalOp(op))),
        };
        let block: Option<&mut Block<Step>> = current.and_then(|number| steps.get_mut(&number));
        if let (Some(block), Some(old), Some(new)) = (block, whole_id(old).map(CanonicalOp), new) {
            let (step, drops, _) = &mut block.read;
            let became = step.entry(old.clone()).or_insert_with(|| {
                if dropped {
                    drops.push(old);
                }
                vec![]
            });
            became.extend(new);
            block.seen += 1;
        }
    }
    steps
}

impl Records {
    /// Reads what `musubi_dir` keeps.
    pub(in super::super) fn load(musubi_dir: &Path) -> Result<Self, NodeError> {
        let path = musubi_dir.join(RECORDS_FILE);
        let file: RecordsFile = match fs::read(&path) {
            Ok(bytes) => serde_json::from_slice(&bytes).map_err(|err| NodeError::Io {
                path: path.clone(),
                source: std::io::Error::other(err),
            })?,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => RecordsFile::default(),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        let applied = file
            .applied
            .iter()
            .map(|record| parse_record(&path, record))
            .collect::<Result<Vec<_>, _>>()?;
        let parse_digest = |hex: &str| {
            jj_lib::hex_util::decode_hex(hex)
                .map(|bytes| RecordDigest::from_bytes(&bytes))
                .ok_or_else(|| NodeError::Io {
                    path: path.clone(),
                    source: std::io::Error::other(format!("bad record digest {hex}")),
                })
        };
        let prefix = match &file.prefix {
            None => RecordPrefix::none(),
            Some((count, hex)) => RecordPrefix {
                count: *count,
                digest: parse_digest(hex)?,
            },
        };
        let entries = |entries: &[(String, Vec<String>)]| {
            entries
                .iter()
                .map(|(before, record)| {
                    let before = parse_digest(before)?;
                    let record = parse_record(&path, record)?;
                    Ok(Earlier {
                        digest: before.then(&record),
                        before,
                        record,
                    })
                })
                .collect::<Result<Vec<_>, NodeError>>()
        };
        let earlier = entries(&file.earlier)?;
        let custody = entries(&file.custody)?;
        let mut records = Self {
            digests: digests(&prefix.digest, &applied),
            prefix,
            applied,
            earlier,
            custody,
            fresh: file.fresh,
            pending: parse_record(&path, &file.pending)?,
            fixup: file.fixup,
            fixup_written: file.fixup_written,
            fixup_from: file
                .fixup_from
                .as_deref()
                .and_then(OperationId::try_from_hex)
                .map(CanonicalOp),
            moving: file.moving,
            realign: file
                .realign
                .as_ref()
                .map(|realign| Realign::from_file(&path, realign))
                .transpose()?,
            ..Self::default()
        };
        // Each log has every block that `records.json`, written after it, counts on, unless a
        // power cut lost some of it.
        let damaged = |path: PathBuf| {
            tracing::error!("{} lacks what records.json counts on", path.display());
            NodeError::DamagedLog
        };
        let path = musubi_dir.join(HUB_RENAMINGS_FILE);
        let mut renamings = parse_hub_renamings(&read_log(&path)?);
        records.hub_renamings = records.digests[1..]
            .iter()
            .map(|digest| {
                let block = renamings.remove(&digest_hex(digest));
                block.and_then(Block::whole)
            })
            .collect::<Option<_>>()
            .ok_or_else(|| damaged(path))?;
        let path = musubi_dir.join(STEPS_FILE);
        let mut steps = parse_steps(&read_log(&path)?);
        for number in 1..=file.steps {
            let Some(step) = steps.remove(&number).and_then(Block::whole) else {
                return Err(damaged(path));
            };
            records.compose(step);
            records.steps = number;
        }
        Ok(records)
    }
}

impl NodeRepo {
    pub(super) fn records_path(&self) -> PathBuf {
        self.repo_path.join("musubi").join(RECORDS_FILE)
    }

    pub(super) fn save_records(&self) -> Result<(), NodeError> {
        let records = &self.records;
        let prefix = &records.prefix;
        let file = RecordsFile {
            prefix: (prefix.count > 0).then(|| (prefix.count, digest_hex(&prefix.digest))),
            fresh: records.fresh,
            applied: records.applied.iter().map(hex_ids).collect(),
            pending: hex_ids(&records.pending),
            fixup: records.fixup.clone(),
            fixup_written: records.fixup_written,
            fixup_from: records.fixup_from.as_ref().map(|op| op.0.hex()),
            moving: records.moving,
            realign: records.realign.as_ref().map(Realign::to_file),
            steps: records.steps,
            earlier: records
                .earlier
                .iter()
                .map(|earlier| (digest_hex(&earlier.before), hex_ids(&earlier.record)))
                .collect(),
            custody: records
                .custody
                .iter()
                .map(|custody| (digest_hex(&custody.before), hex_ids(&custody.record)))
                .collect(),
        };
        let path = self.records_path();
        let bytes = serde_json::to_vec_pretty(&file).map_err(|err| NodeError::Io {
            path: path.clone(),
            source: std::io::Error::other(err),
        })?;
        files::replace(&path, &bytes).map_err(|source| NodeError::Io { path, source })
    }

    /// Records a renaming, which dropped `dropped`: appends it, in one write, and composes it.
    pub(super) fn add_step(
        &mut self,
        step: HashMap<CanonicalOp, Vec<CanonicalOp>>,
        dropped: &HashSet<CanonicalOp>,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<(), NodeError> {
        if let Some(step) = self.append_step(step, dropped, counterparts)? {
            self.records.compose(step);
            self.records.steps += 1;
        }
        Ok(())
    }

    /// Appends a renaming, which dropped `dropped`, to the steps log, in one write, as the
    /// next step, which `records.json` counts once saved. Returns it, as composed, unless it
    /// changes nothing.
    pub(super) fn append_step(
        &self,
        step: HashMap<CanonicalOp, Vec<CanonicalOp>>,
        dropped: &HashSet<CanonicalOp>,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<Option<Step>, NodeError> {
        let step: HashMap<CanonicalOp, Vec<CanonicalOp>> = step
            .into_iter()
            .filter(|(old, new)| new != std::slice::from_ref(old))
            .collect();
        let sources: HashMap<LocalOp, CanonicalOp> = counterparts
            .iter()
            .filter(|(_, old)| !dropped.contains(*old))
            .filter_map(|(source, old)| {
                let current = match step.get(old).map(Vec::as_slice) {
                    Some([current]) => current,
                    None => old,
                    Some(_) => return None,
                };
                (self.records.sources.get(source) != Some(current))
                    .then(|| (source.clone(), current.clone()))
            })
            .collect();
        if step.is_empty() && sources.is_empty() {
            return Ok(None);
        }
        let path = self.repo_path.join("musubi").join(STEPS_FILE);
        append_log(
            &path,
            &format_step(self.records.steps + 1, &step, dropped, &sources),
        )?;
        let dropped = step
            .keys()
            .filter(|old| dropped.contains(*old))
            .cloned()
            .collect();
        Ok(Some((step, dropped, sources)))
    }

    /// Appends how the records of `records`, after the records `start` is the digest of,
    /// from the `from`th on renamed the hub's history, in one write.
    pub(super) fn write_hub_renamings(
        &self,
        start: &RecordDigest,
        records: &[Record],
        from: usize,
        renamings: &[HashMap<CanonicalOp, CanonicalOp>],
    ) -> Result<(), NodeError> {
        if renamings.is_empty() {
            return Ok(());
        }
        let path = self.repo_path.join("musubi").join(HUB_RENAMINGS_FILE);
        append_log(
            &path,
            &format_hub_renamings(start, records, from, renamings),
        )
    }
}
