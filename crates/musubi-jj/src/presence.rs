//! Which copies a hive shows: the rule of `formal/Musubi/Presence.lean` (docs/internals/design.md,
//! "Copies that go away").
//!
//! An operation may be *work* by a copy, one its own `jj` made or musubi made for it, as its
//! join, or a *forget* of copies, as `musubi forget` and `musubi leave` write. A copy is present
//! at an operation when some of its work in the operation's history is in the history of no
//! forget of it there: a forget removes the work it saw, and only work brings a copy back.
//!
//! [`Presence`] keeps, for each copy present at an operation, its latest work that no forget saw
//! (`UMax` in the model), which decides presence at the operation's descendants without walking
//! the history again: [`Presence::merge`] and [`Presence::apply`] are `umax_merge`,
//! `umax_work` and `umax_forget`. It keeps each copy's latest work, whether or not a forget saw
//! it, too ([`Presence::worked`]), and the `musubi.forget-after` the copy last recorded
//! ([`Presence::forget_after`]), which the model leaves out: they decide nothing about
//! presence, only what a forgotten copy's own workspaces are, and when a daemon forgets a
//! copy that has gone unused. It keeps, too, each copy's latest records of its name
//! ([`Presence::name`]): `NameIs` in formal/Musubi/Identity.lean, which decides the names its
//! workspaces are shown under (`crate::workspaces::display_names`).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;
use std::time::Duration;

use jiff::SignedDuration;
use jiff::Span;
use jiff::SpanRelativeTo;
use jiff::SpanRound;
use jiff::Unit;
use jiff::fmt::friendly::SpanParser;
use jiff::fmt::friendly::SpanPrinter;
use jj_lib::op_store::OperationMetadata;

use crate::workspaces;

/// The attribute of an operation that forgets copies: their machine keys, separated by spaces.
pub const FORGET_ATTRIBUTE: &str = "musubi.forget";

/// The attribute of an operation musubi writes as a copy's own work, such as its join: the
/// copy's machine key.
pub const WORK_ATTRIBUTE: &str = "musubi.work";

/// The attribute of an operation recording its copy's `musubi.forget-after`, as
/// [`format_forget_after`] writes it: how long the copy may go unused before a daemon forgets
/// it. The operation is the copy's work, and changes nothing else.
pub const FORGET_AFTER_ATTRIBUTE: &str = "musubi.forget-after";

/// The attribute of an operation recording its copy's name, as `workspaces::sanitize` makes
/// it: what the copy's workspaces are shown under from there on, until it records another.
/// The operation is the copy's work, and changes nothing else.
pub const NAME_ATTRIBUTE: &str = "musubi.name";

/// A month and a year in seconds, as `humantime` took them (30.44 and 365.25 days), which
/// earlier builds recorded in hives' operation metadata.
const MONTH_SECS: u64 = 2_630_016;
const YEAR_SECS: u64 = 31_557_600;

/// How long a copy may go unused before a daemon forgets it, `None` for never: from
/// `never`, or a duration in jiff's friendly format, such as `6h`, `1h 30m`, `2 days` or `1w`,
/// of at least a second. Units run from seconds to years, a day being 24 hours, a week 7 days,
/// a month 30.44 days and a year 365.25 days, as `humantime` took them. A negative duration is
/// refused.
pub fn parse_forget_after(text: &str) -> Result<Option<Duration>, BadForgetAfter> {
    let text = text.trim();
    if text == "never" {
        return Ok(None);
    }
    let after = parse_duration(text).ok_or(BadForgetAfter::NotADuration)?;
    if after < Duration::from_secs(1) {
        return Err(BadForgetAfter::TooShort);
    }
    Ok(Some(after))
}

fn parse_duration(text: &str) -> Option<Duration> {
    let span = SpanParser::new().parse_span(text).ok()?;
    let fixed = SignedDuration::from_secs(i64::from(span.get_years()) * YEAR_SECS as i64)
        .checked_add(SignedDuration::from_secs(
            i64::from(span.get_months()) * MONTH_SECS as i64,
        ))?;
    let rest = span
        .years(0)
        .months(0)
        .to_duration(SpanRelativeTo::days_are_24_hours())
        .ok()?;
    Duration::try_from(fixed.checked_add(rest)?).ok()
}

/// Why a `musubi.forget-after` can't be read, as a message says after naming it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BadForgetAfter {
    #[error("is neither `never` nor a duration such as `6h`")]
    NotADuration,
    #[error("is shorter than a second, the least it can be")]
    TooShort,
}

/// A `musubi.forget-after` as [`parse_forget_after`] reads it: `6h`, `1h 30m`, `never`. Whole
/// years and months come first, at the lengths above, then weeks, days, hours, minutes and
/// seconds, a day being 24 hours: `1mo`, `2d`, `1w 1d 1s`.
pub fn format_forget_after(after: Option<Duration>) -> String {
    let Some(after) = after else {
        return "never".to_owned();
    };
    let secs = after.as_secs();
    let years = secs / YEAR_SECS;
    let months = secs % YEAR_SECS / MONTH_SECS;
    let rest = after - Duration::from_secs(years * YEAR_SECS + months * MONTH_SECS);
    let printer = SpanPrinter::new();
    let mut parts = Vec::new();
    if years > 0 {
        parts.push(format!("{years}y"));
    }
    if months > 0 {
        parts.push(format!("{months}mo"));
    }
    if !rest.is_zero() || parts.is_empty() {
        let span = Span::try_from(rest).and_then(|span| {
            span.round(
                SpanRound::new()
                    .largest(Unit::Week)
                    .relative(SpanRelativeTo::days_are_24_hours()),
            )
        });
        parts.push(match span {
            Ok(span) => printer.span_to_string(&span),
            Err(_) => printer.unsigned_duration_to_string(&rest),
        });
    }
    parts.join(" ")
}

/// What an operation is to presence: whose work it is, which copies it forgets, and the
/// `musubi.forget-after` and name it records for the copy whose work it is.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Kind {
    pub work: Option<String>,
    pub forgets: BTreeSet<String>,
    pub forget_after: Option<Option<Duration>>,
    pub name: Option<String>,
}

impl Kind {
    /// The kind of a canonical operation: work by the copy whose workspace made it, or that
    /// [`WORK_ATTRIBUTE`] names, and a forget of the copies [`FORGET_ATTRIBUTE`] names. A
    /// copy is named by a machine key, which is never empty and has no whitespace: a name
    /// that isn't one names no copy, so that presence can always be written down as a stamp.
    pub fn of(metadata: &OperationMetadata) -> Self {
        let is_key = |key: &String| !key.is_empty() && !key.contains(char::is_whitespace);
        let work = metadata
            .workspace_name
            .as_ref()
            .and_then(|key| workspaces::split_key(key.as_str()))
            .map(|(machine, _)| machine.to_owned())
            .or_else(|| metadata.attributes.get(WORK_ATTRIBUTE).cloned())
            .filter(is_key);
        let forgets = metadata
            .attributes
            .get(FORGET_ATTRIBUTE)
            .map(|keys| keys.split_whitespace().map(str::to_owned).collect())
            .unwrap_or_default();
        let forget_after = metadata
            .attributes
            .get(FORGET_AFTER_ATTRIBUTE)
            .and_then(|text| parse_forget_after(text).ok());
        // Only a name `sanitize` leaves as it is: one with a `/` or a space, from a buggy or
        // hostile peer, would make names that aren't one workspace's, or stamps that don't
        // read.
        let name = metadata
            .attributes
            .get(NAME_ATTRIBUTE)
            .filter(|name| workspaces::sanitize(name) == **name)
            .cloned();
        Self {
            work,
            forgets,
            forget_after,
            name,
        }
    }
}

/// The copies present at an operation, each with its latest work that no forget saw. A copy
/// present has at least one; usually it has exactly one, its latest work. With them, every
/// copy the operation's history has known, present or not, by whose work or forget, and each
/// one's latest work, whether or not a forget saw it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Presence<Op> {
    latest: BTreeMap<String, BTreeSet<Op>>,
    known: Arc<BTreeSet<String>>,
    worked: Arc<BTreeMap<String, BTreeSet<Op>>>,
    /// Each copy's latest operations recording its `musubi.forget-after`, with what they
    /// record.
    forget_after: Arc<BTreeMap<String, BTreeMap<Op, Option<Duration>>>>,
    /// Each copy's latest operations recording its name, with the name they record.
    names: Arc<BTreeMap<String, BTreeMap<Op, String>>>,
}

impl<Op> Default for Presence<Op> {
    fn default() -> Self {
        Self {
            latest: BTreeMap::new(),
            known: Arc::default(),
            worked: Arc::default(),
            forget_after: Arc::default(),
            names: Arc::default(),
        }
    }
}

impl<Op: Clone + Ord> Presence<Op> {
    pub fn is_present(&self, copy: &str) -> bool {
        self.latest.contains_key(copy)
    }

    /// The copies present, in order.
    pub fn copies(&self) -> impl Iterator<Item = &str> {
        self.latest.keys().map(String::as_str)
    }

    /// A present copy's latest work that no forget saw.
    pub fn latest(&self, copy: &str) -> Option<&BTreeSet<Op>> {
        self.latest.get(copy)
    }

    /// Every copy the history has known: worked, joined, or been forgotten.
    pub fn known(&self) -> &BTreeSet<String> {
        &self.known
    }

    /// A copy's latest work in the history, whether or not a forget saw it: what it last
    /// did, as of an operation where it is forgotten. Usually one operation; more where the
    /// copy worked on two lines of history that a merge joined.
    pub fn worked(&self, copy: &str) -> Option<&BTreeSet<Op>> {
        self.worked.get(copy)
    }

    /// How long a copy may go unused before a daemon forgets it, as it last recorded
    /// (`None` for never, as for a copy that has recorded nothing). Where it recorded
    /// different values on two lines of history that a merge joined, the longer.
    pub fn forget_after(&self, copy: &str) -> Option<Duration> {
        let records = self.forget_after.get(copy)?;
        let mut longest = Some(Duration::ZERO);
        for after in records.values() {
            longest = match (longest, after) {
                (Some(a), Some(b)) => Some(a.max(*b)),
                _ => None,
            };
        }
        longest
    }

    /// Whether a copy has recorded a `musubi.forget-after`.
    pub fn has_forget_after(&self, copy: &str) -> bool {
        self.forget_after.contains_key(copy)
    }

    /// The name a copy last recorded: the greatest of its latest records, where it recorded
    /// different names on two lines of history that a merge joined; none if it has recorded
    /// none. Forgets leave it, so a copy that comes back keeps its name.
    pub fn recorded_name(&self, copy: &str) -> Option<&str> {
        self.names.get(copy)?.values().map(String::as_str).max()
    }

    /// A copy's name (`NameIs`): the one it last recorded, else the one its key embeds.
    pub fn name<'a>(&'a self, copy: &'a str) -> &'a str {
        self.recorded_name(copy)
            .unwrap_or_else(|| workspaces::machine_name(copy))
    }

    /// The copies present, each with its name, as `workspaces::display_names` takes them.
    pub fn named(&self) -> BTreeMap<String, String> {
        self.copies()
            .map(|copy| (copy.to_owned(), self.name(copy).to_owned()))
            .collect()
    }

    /// The machines named at an operation with this presence: the copies present, and any
    /// other with workspaces in its view, `in_view`, as one that joined before joining was
    /// recorded as work, each with its name there. Nodes and hubs name the same machines so.
    pub fn named_with<'a>(
        &self,
        in_view: impl IntoIterator<Item = &'a str>,
    ) -> BTreeMap<String, String> {
        let mut machines = self.named();
        for machine in in_view {
            machines
                .entry(machine.to_owned())
                .or_insert_with(|| self.name(machine).to_owned());
        }
        machines
    }

    /// Presence before an operation's own effect, from its parents' (`umax_merge`): the
    /// latest work of each copy that the parents keep, each kept unless a parent whose
    /// history has it doesn't keep it, as when a forget there saw it, or later work there
    /// followed it. One parent's is the operation's. Each copy's latest work regardless of
    /// forgets is the parents' latest, but for any that is an ancestor of another.
    /// `is_ancestor(a, b)` is whether `a` is `b` or an ancestor of it.
    pub fn merge<E>(
        parents: &[(Op, &Self)],
        mut is_ancestor: impl FnMut(&Op, &Op) -> Result<bool, E>,
    ) -> Result<Self, E> {
        match parents {
            [] => return Ok(Self::default()),
            [(_, only)] => return Ok((*only).clone()),
            _ => {}
        }
        let mut known = parents[0].1.known.clone();
        let mut worked = parents[0].1.worked.clone();
        let mut forget_after = parents[0].1.forget_after.clone();
        let mut names = parents[0].1.names.clone();
        for (_, presence) in &parents[1..] {
            if !Arc::ptr_eq(&names, &presence.names) {
                for (copy, records) in presence.names.iter() {
                    let merged = match names.get(copy) {
                        None => records.clone(),
                        Some(have) if records.keys().all(|op| have.contains_key(op)) => continue,
                        Some(have) => latest_records(have, records, &mut is_ancestor)?,
                    };
                    Arc::make_mut(&mut names).insert(copy.clone(), merged);
                }
            }
            if !Arc::ptr_eq(&known, &presence.known) && !known.is_superset(&presence.known) {
                Arc::make_mut(&mut known).extend(presence.known.iter().cloned());
            }
            if !Arc::ptr_eq(&worked, &presence.worked) {
                for (copy, ops) in presence.worked.iter() {
                    let merged = match worked.get(copy) {
                        None => ops.clone(),
                        Some(have) if have.is_superset(ops) => continue,
                        Some(have) => latest_of(have, ops, &mut is_ancestor)?,
                    };
                    Arc::make_mut(&mut worked).insert(copy.clone(), merged);
                }
            }
            if !Arc::ptr_eq(&forget_after, &presence.forget_after) {
                for (copy, records) in presence.forget_after.iter() {
                    let merged = match forget_after.get(copy) {
                        None => records.clone(),
                        Some(have) if records.keys().all(|op| have.contains_key(op)) => continue,
                        Some(have) => latest_records(have, records, &mut is_ancestor)?,
                    };
                    Arc::make_mut(&mut forget_after).insert(copy.clone(), merged);
                }
            }
        }
        let copies: BTreeSet<&String> = parents
            .iter()
            .flat_map(|(_, presence)| presence.latest.keys())
            .collect();
        let mut latest = BTreeMap::new();
        for copy in copies {
            let candidates: BTreeSet<&Op> = parents
                .iter()
                .filter_map(|(_, presence)| presence.latest.get(copy))
                .flatten()
                .collect();
            let mut kept = BTreeSet::new();
            'candidates: for &candidate in &candidates {
                for (op, presence) in parents {
                    let has = presence
                        .latest
                        .get(copy)
                        .is_some_and(|ops| ops.contains(candidate));
                    if !has && is_ancestor(candidate, op)? {
                        continue 'candidates;
                    }
                }
                kept.insert(candidate.clone());
            }
            if !kept.is_empty() {
                latest.insert(copy.clone(), kept);
            }
        }
        Ok(Self {
            latest,
            known,
            worked,
            forget_after,
            names,
        })
    }

    /// This presence as an earlier release's contraction stamped an operation with it, and as a
    /// cleanup compares presences, each operation as `name` writes it: a line for each
    /// copy known, each copy's latest work that no forget saw, its latest work whether or not
    /// one did, the `musubi.forget-after` it last recorded, and its latest records of its
    /// name, in order. Earlier releases wrote no records of names.
    pub fn to_stamp(&self, name: impl Fn(&Op) -> String) -> String {
        let mut lines = vec![];
        for copy in self.known.iter() {
            lines.push(format!("known {copy}"));
        }
        for (copy, ops) in &self.latest {
            lines.extend(ops.iter().map(|op| format!("latest {copy} {}", name(op))));
        }
        for (copy, ops) in self.worked.iter() {
            lines.extend(ops.iter().map(|op| format!("worked {copy} {}", name(op))));
        }
        for (copy, records) in self.forget_after.iter() {
            for (op, after) in records {
                let after = match after {
                    Some(after) => format!("{}.{:09}", after.as_secs(), after.subsec_nanos()),
                    None => "never".to_owned(),
                };
                lines.push(format!("forget-after {copy} {} {after}", name(op)));
            }
        }
        for (copy, records) in self.names.iter() {
            for (op, recorded) in records {
                lines.push(format!("name {copy} {} {recorded}", name(op)));
            }
        }
        lines.join("\n")
    }

    /// The presence a stamp [`Self::to_stamp`] wrote has, each operation as `parse` reads one.
    /// None if it isn't such a stamp, or not as [`Self::to_stamp`] would write it.
    pub fn from_stamp(
        text: &str,
        name: impl Fn(&Op) -> String,
        parse: impl Fn(&str) -> Option<Op>,
    ) -> Option<Self> {
        let mut presence = Self::default();
        let mut known = BTreeSet::new();
        let mut worked: BTreeMap<String, BTreeSet<Op>> = BTreeMap::new();
        let mut forget_after: BTreeMap<String, BTreeMap<Op, Option<Duration>>> = BTreeMap::new();
        let mut names: BTreeMap<String, BTreeMap<Op, String>> = BTreeMap::new();
        for line in text.split('\n') {
            let words: Vec<&str> = line.split(' ').collect();
            if words.iter().any(|word| word.is_empty()) {
                return None;
            }
            match words.as_slice() {
                ["known", copy] => {
                    known.insert((*copy).to_owned());
                }
                ["latest", copy, op] => {
                    presence
                        .latest
                        .entry((*copy).to_owned())
                        .or_default()
                        .insert(parse(op)?);
                }
                ["worked", copy, op] => {
                    worked
                        .entry((*copy).to_owned())
                        .or_default()
                        .insert(parse(op)?);
                }
                ["forget-after", copy, op, after] => {
                    let after = match *after {
                        "never" => None,
                        after => {
                            let (secs, nanos) = after.split_once('.')?;
                            if nanos.len() != 9 {
                                return None;
                            }
                            Some(Duration::new(secs.parse().ok()?, nanos.parse().ok()?))
                        }
                    };
                    forget_after
                        .entry((*copy).to_owned())
                        .or_default()
                        .insert(parse(op)?, after);
                }
                ["name", copy, op, recorded] => {
                    names
                        .entry((*copy).to_owned())
                        .or_default()
                        .insert(parse(op)?, (*recorded).to_owned());
                }
                _ => return None,
            }
        }
        presence.known = Arc::new(known);
        presence.worked = Arc::new(worked);
        presence.forget_after = Arc::new(forget_after);
        presence.names = Arc::new(names);
        // One encoding for each presence, so that equal presences stamp equal operations.
        (presence.to_stamp(name) == text).then_some(presence)
    }

    /// Every operation this presence names for `copy`.
    pub fn ops_of<'a>(&'a self, copy: &'a str) -> impl Iterator<Item = &'a Op> {
        self.latest
            .get(copy)
            .into_iter()
            .flatten()
            .chain(self.worked.get(copy).into_iter().flatten())
            .chain(
                self.forget_after
                    .get(copy)
                    .into_iter()
                    .flat_map(BTreeMap::keys),
            )
            .chain(self.names.get(copy).into_iter().flat_map(BTreeMap::keys))
    }

    /// Every operation this presence names.
    pub fn ops(&self) -> impl Iterator<Item = &Op> {
        self.latest
            .values()
            .flatten()
            .chain(self.worked.values().flatten())
            .chain(self.forget_after.values().flat_map(BTreeMap::keys))
            .chain(self.names.values().flat_map(BTreeMap::keys))
    }

    /// Presence at operation `op` of `kind`, from [`Self::merge`] of its parents': its work is
    /// its copy's latest (`umax_work`), and the copies it forgets are absent (`umax_forget`).
    pub fn apply(mut self, op: &Op, kind: &Kind) -> Self {
        for copy in kind.work.iter().chain(&kind.forgets) {
            if !self.known.contains(copy) {
                Arc::make_mut(&mut self.known).insert(copy.clone());
            }
        }
        if let Some(copy) = &kind.work {
            if let Some(name) = &kind.name {
                Arc::make_mut(&mut self.names)
                    .insert(copy.clone(), BTreeMap::from([(op.clone(), name.clone())]));
            }
            self.latest
                .insert(copy.clone(), BTreeSet::from([op.clone()]));
            Arc::make_mut(&mut self.worked).insert(copy.clone(), BTreeSet::from([op.clone()]));
            if let Some(after) = kind.forget_after {
                Arc::make_mut(&mut self.forget_after)
                    .insert(copy.clone(), BTreeMap::from([(op.clone(), after)]));
            }
        }
        for copy in &kind.forgets {
            self.latest.remove(copy);
        }
        self
    }
}

/// The latest of two sets of records, each its own latest already, with what each records
/// (`latest_of`).
fn latest_records<Op: Clone + Ord, T: Clone, E>(
    have: &BTreeMap<Op, T>,
    theirs: &BTreeMap<Op, T>,
    is_ancestor: &mut impl FnMut(&Op, &Op) -> Result<bool, E>,
) -> Result<BTreeMap<Op, T>, E> {
    let ops = latest_of(
        &have.keys().cloned().collect(),
        &theirs.keys().cloned().collect(),
        is_ancestor,
    )?;
    Ok(ops
        .into_iter()
        .map(|op| {
            let value = have.get(&op).or_else(|| theirs.get(&op));
            let value = value.expect("an operation from either side").clone();
            (op, value)
        })
        .collect())
}

/// The latest of two sets of operations, each its own latest already: their union, but for
/// any that is an ancestor of one only the other has.
fn latest_of<Op: Clone + Ord, E>(
    have: &BTreeSet<Op>,
    theirs: &BTreeSet<Op>,
    is_ancestor: &mut impl FnMut(&Op, &Op) -> Result<bool, E>,
) -> Result<BTreeSet<Op>, E> {
    let new: Vec<&Op> = theirs.difference(have).collect();
    let mut older: BTreeSet<&Op> = BTreeSet::new();
    for a in have.difference(theirs) {
        for &b in &new {
            if is_ancestor(a, b)? {
                older.insert(a);
            } else if is_ancestor(b, a)? {
                older.insert(b);
            }
        }
    }
    Ok(have
        .iter()
        .chain(new)
        .filter(|op| !older.contains(op))
        .cloned()
        .collect())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::convert::Infallible;

    use super::*;

    /// A stamp reads back as the presence it was written from, and only the one way of writing
    /// each presence reads at all, so that equal presences stamp equal operations.
    #[test]
    fn stamps_read_back_and_only_as_written() {
        let work = |copy: &str| Kind {
            work: Some(copy.to_owned()),
            ..Kind::default()
        };
        let forget = |copy: &str| Kind {
            forgets: BTreeSet::from([copy.to_owned()]),
            ..Kind::default()
        };
        let mut presence = Presence::<usize>::default().apply(&1, &work("a"));
        let mut recorded = work("b");
        recorded.forget_after = Some(Some(Duration::new(3600, 5)));
        recorded.name = Some("desk".to_owned());
        presence = presence.apply(&2, &recorded).apply(&3, &forget("a"));
        let mut never = work("c");
        never.forget_after = Some(None);
        presence = presence.apply(&4, &never);
        let name = |op: &usize| op.to_string();
        let parse = |text: &str| text.parse().ok();
        let stamp = presence.to_stamp(name);
        assert_eq!(
            stamp,
            "known a\nknown b\nknown c\nlatest b 2\nlatest c 4\nworked a 1\nworked b 2\n\
             worked c 4\nforget-after b 2 3600.000000005\nforget-after c 4 never\n\
             name b 2 desk"
        );
        assert_eq!(Presence::from_stamp(&stamp, name, parse), Some(presence));
        for other in [
            "known b\nknown a",
            "known a\n",
            "known  a",
            "known a b",
            "latest a x",
            "forget-after a 1 3600",
            "forget-after a 1 3600.5",
            "name a 1",
            "present a",
        ] {
            assert_eq!(
                Presence::<usize>::from_stamp(other, name, parse),
                None,
                "{other:?}"
            );
        }
    }

    /// `parents[x]` are `x`'s parents, all smaller.
    fn ancestor(parents: &[Vec<usize>]) -> impl Fn(&usize, &usize) -> Result<bool, Infallible> {
        move |&a, &b| {
            let mut stack = vec![b];
            while let Some(x) = stack.pop() {
                if x == a {
                    return Ok(true);
                }
                stack.extend(parents[x].iter().filter(|&&p| p >= a));
            }
            Ok(false)
        }
    }

    fn presences(parents: &[Vec<usize>], kinds: &[Kind]) -> Vec<Presence<usize>> {
        let mut out: Vec<Presence<usize>> = vec![];
        for (x, kind) in kinds.iter().enumerate() {
            let ps: Vec<(usize, &Presence<usize>)> =
                parents[x].iter().map(|&p| (p, &out[p])).collect();
            let merged = Presence::merge(&ps, ancestor(parents)).unwrap();
            out.push(merged.apply(&x, kind));
        }
        out
    }

    fn work(copy: &str) -> Kind {
        Kind {
            work: Some(copy.to_owned()),
            ..Kind::default()
        }
    }

    fn forget(copy: &str) -> Kind {
        Kind {
            forgets: BTreeSet::from([copy.to_owned()]),
            ..Kind::default()
        }
    }

    /// A copy's latest work, whatever forgets saw: its work replaces it, forgets leave it, and
    /// a merge keeps each line's latest, but for one the other line has seen.
    #[test]
    fn worked_is_the_latest_work_through_forgets() {
        let parents = vec![
            vec![],     // 0: k works
            vec![0],    // 1: k works again
            vec![0],    // 2: a daemon forgets k, having seen only 0
            vec![1, 2], // 3: merge
            vec![1],    // 4: a daemon forgets k, having seen 1
            vec![0],    // 5: k works on another line
            vec![4, 5], // 6: merge
        ];
        let kinds = vec![
            work("k"),
            work("k"),
            forget("k"),
            Kind::default(),
            forget("k"),
            work("k"),
            Kind::default(),
        ];
        let p = presences(&parents, &kinds);
        assert_eq!(p[2].worked("k"), Some(&BTreeSet::from([0])));
        assert_eq!(p[3].worked("k"), Some(&BTreeSet::from([1])));
        assert!(!p[4].is_present("k"));
        assert_eq!(p[4].worked("k"), Some(&BTreeSet::from([1])));
        assert_eq!(p[6].worked("k"), Some(&BTreeSet::from([1, 5])));
    }

    #[test]
    fn forget_after_reads_and_writes() {
        let secs = |n: u64| Ok(Some(Duration::from_secs(n)));
        for (text, expected) in [
            ("6h", 6 * 3600),
            ("6 hours", 6 * 3600),
            (" 1h 30m ", 5400),
            ("1h30m", 5400),
            ("2 days", 48 * 3600),
            ("2days", 48 * 3600),
            ("1w", 7 * 24 * 3600),
            ("1 week", 7 * 24 * 3600),
            ("1w 1d 1s", 8 * 24 * 3600 + 1),
            ("45s", 45),
            // Months and years as `humantime` read them, and wrote them in earlier builds.
            ("1month", MONTH_SECS),
            ("2months", 2 * MONTH_SECS),
            ("1mo", MONTH_SECS),
            ("1year", YEAR_SECS),
            ("7years", 7 * YEAR_SECS),
            ("1y", YEAR_SECS),
            ("1yr", YEAR_SECS),
            ("1month 5h 2m 3s", MONTH_SECS + 5 * 3600 + 2 * 60 + 3),
            (
                "1year 2months 3days 4h 5m 6s",
                YEAR_SECS + 2 * MONTH_SECS + 3 * 86400 + 4 * 3600 + 5 * 60 + 6,
            ),
        ] {
            assert_eq!(parse_forget_after(text), secs(expected), "{text:?}");
        }
        assert_eq!(parse_forget_after("never"), Ok(None));
        for bad in ["", "6", "h", "6x", "-1h", "-1month", "Never", "1M", "M"] {
            assert_eq!(
                parse_forget_after(bad),
                Err(BadForgetAfter::NotADuration),
                "{bad:?}"
            );
        }
        for short in ["0h", "0s", "500ms"] {
            assert_eq!(
                parse_forget_after(short),
                Err(BadForgetAfter::TooShort),
                "{short:?}"
            );
        }
        assert_eq!(
            format_forget_after(Some(Duration::from_secs(6 * 3600))),
            "6h"
        );
        assert_eq!(
            format_forget_after(Some(Duration::from_secs(5400))),
            "1h 30m"
        );
        for (secs, printed) in [
            (45, "45s"),
            (48 * 3600, "2d"),
            (7 * 24 * 3600, "1w"),
            (8 * 24 * 3600 + 1, "1w 1d 1s"),
            (MONTH_SECS, "1mo"),
            (MONTH_SECS - 1, "4w 2d 10h 33m 35s"),
            (2 * MONTH_SECS + 86400, "2mo 1d"),
            (YEAR_SECS, "1y"),
            (YEAR_SECS + MONTH_SECS + 5 * 3600, "1y 1mo 5h"),
            (3 * YEAR_SECS + 11 * MONTH_SECS + 1, "3y 11mo 1s"),
        ] {
            assert_eq!(
                format_forget_after(Some(Duration::from_secs(secs))),
                printed
            );
        }
        assert_eq!(format_forget_after(None), "never");
        for text in [
            "6h",
            "1h 30m",
            "9days",
            "45s",
            "1week",
            "1w 1d 1s",
            "2d",
            "never",
            "1month",
            "2months",
            "1year 2months 3days 4h 5m 6s",
            "1y 11mo 4w 2d 10h",
            "7years",
        ] {
            let after = parse_forget_after(text).unwrap();
            assert_eq!(parse_forget_after(&format_forget_after(after)), Ok(after));
        }
    }

    /// A copy's `musubi.forget-after` is the last it recorded, which forgets leave; where
    /// it recorded two on lines a merge joins, the longer; never, if it recorded none.
    #[test]
    fn forget_after_is_the_last_recorded() {
        let set = |copy: &str, after: Option<u64>| Kind {
            forget_after: Some(after.map(|h| Duration::from_secs(h * 3600))),
            ..work(copy)
        };
        let parents = vec![
            vec![],     // 0: k works
            vec![0],    // 1: k records 6h
            vec![1],    // 2: a daemon forgets k
            vec![1],    // 3: k records 1h
            vec![0],    // 4: k, on another line, records 2h
            vec![3, 4], // 5: merge
            vec![2, 3], // 6: merge
        ];
        let kinds = vec![
            work("k"),
            set("k", Some(6)),
            forget("k"),
            set("k", Some(1)),
            set("k", Some(2)),
            Kind::default(),
            Kind::default(),
        ];
        let p = presences(&parents, &kinds);
        let hours = |h: u64| Some(Duration::from_secs(h * 3600));
        assert_eq!(p[0].forget_after("k"), None);
        assert!(!p[0].has_forget_after("k"));
        assert_eq!(p[2].forget_after("k"), hours(6));
        assert_eq!(p[5].forget_after("k"), hours(2));
        assert_eq!(p[6].forget_after("k"), hours(1));
    }

    /// A copy's name is the last it recorded, which forgets leave; where it recorded two on
    /// lines a merge joins, the greater; the one its key embeds, if it recorded none.
    #[test]
    fn names_are_the_latest_records() {
        let name = |copy: &str, name: &str| Kind {
            name: Some(name.to_owned()),
            ..work(copy)
        };
        let parents = vec![
            vec![],     // 0: k#1 joins
            vec![0],    // 1: k#1 records `desk`
            vec![1],    // 2: a daemon forgets k#1
            vec![2],    // 3: k#1 works again, returning
            vec![0],    // 4: k#1, on another line, records `alpha`
            vec![3, 4], // 5: merge
            vec![5],    // 6: k#1 works
        ];
        let kinds = vec![
            work("k#1"),
            name("k#1", "desk"),
            forget("k#1"),
            work("k#1"),
            name("k#1", "alpha"),
            Kind::default(),
            work("k#1"),
        ];
        let p = presences(&parents, &kinds);
        assert_eq!(p[0].name("k#1"), "k");
        assert_eq!(p[0].recorded_name("k#1"), None);
        let names: Vec<&str> = p[1..].iter().map(|p| p.name("k#1")).collect();
        assert_eq!(names, ["desk", "desk", "desk", "alpha", "desk", "desk"]);
    }

    /// A forget concurrent with work it didn't see leaves the copy present; one that saw all
    /// of it doesn't, and nothing but more work brings it back.
    #[test]
    fn forgets_remove_only_what_they_saw() {
        let parents = vec![
            vec![],     // 0: k works
            vec![0],    // 1: a daemon forgets k
            vec![0],    // 2: k works again, concurrently
            vec![1, 2], // 3: merge
            vec![1],    // 4: k's daemon writes something of its own
            vec![3, 4], // 5: merge
        ];
        let kinds = vec![
            work("k"),
            forget("k"),
            work("k"),
            Kind::default(),
            Kind::default(),
            Kind::default(),
        ];
        let p = presences(&parents, &kinds);
        assert!(p[0].is_present("k"));
        assert!(!p[1].is_present("k"));
        assert_eq!(p[3].latest("k"), Some(&BTreeSet::from([2])));
        assert!(!p[4].is_present("k"));
        assert_eq!(p[5].latest("k"), Some(&BTreeSet::from([2])));
    }
}
