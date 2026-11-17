//! Conservative witnesses from adjacent local rules and their captured native effects.
//!
//! Absence from today's operation ancestry cannot prove concurrency after an abandon.
//! Instead, the two commands must be adjacent eligible rules on distinct copies, with no
//! synchronization, operation-history contraction or unrelated command between them. Local
//! preparation observations may snapshot or reconcile. Both commands must actually rewrite
//! the same exact input; neither may include the other's operation in its input.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::{Operation, OperationId};
use musubi_jj::node::CANONICAL_ATTRIBUTE;

use crate::identity::SourceKey;
use crate::world::CommandSnapshot;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Race {
    SameChangeRewritten,
    ConcurrentSquashes,
}

impl Race {
    pub(super) const ALL: [Self; 2] = [Self::SameChangeRewritten, Self::ConcurrentSquashes];

    pub(super) fn catalogue_name(self) -> &'static str {
        match self {
            Self::SameChangeRewritten => "same_change_rewritten_on_two_machines",
            Self::ConcurrentSquashes => "both_machines_squash_into_the_same_commit",
        }
    }

    fn rule(self) -> &'static str {
        match self {
            Self::SameChangeRewritten => "describe",
            Self::ConcurrentSquashes => "squash_into",
        }
    }
}

/// Facts captured from an unmarked native operation, not from a requested command alone.
#[derive(Clone, Debug)]
struct Effect {
    copy: String,
    operation: OperationId,
    parent: OperationId,
    key: SourceKey,
    input: CommitId,
    output: CommitId,
    sources: BTreeSet<CommitId>,
}

impl Effect {
    fn of(race: Race, op: &Operation, snapshot: &CommandSnapshot) -> Option<Self> {
        if op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
            || op.parents.as_slice() != std::slice::from_ref(&snapshot.parent)
            || op.commit_predecessors != snapshot.predecessors
        {
            return None;
        }
        let prefix = match race {
            Race::SameChangeRewritten => "describe commit ",
            Race::ConcurrentSquashes => "squash commits into ",
        };
        let input = CommitId::try_from_hex(op.metadata.description.strip_prefix(prefix)?)?;
        let mut successors = snapshot
            .predecessors
            .as_ref()?
            .iter()
            .filter(|(new, old)| **new != input && old.contains(&input));
        let (output, predecessors) = successors.next()?;
        if successors.next().is_some() {
            return None;
        }
        let sources: BTreeSet<_> = predecessors
            .iter()
            .filter(|id| **id != input)
            .cloned()
            .collect();
        if race == Race::ConcurrentSquashes && sources.is_empty() {
            return None;
        }
        Some(Self {
            copy: snapshot.copy.clone(),
            operation: snapshot.id.clone(),
            parent: snapshot.parent.clone(),
            key: SourceKey::of(op),
            input,
            output: output.clone(),
            sources,
        })
    }
}

#[derive(Clone, Debug)]
pub(super) struct Witness {
    first_rule: u64,
    first: Effect,
    second: Effect,
}

impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "adjacent local rules {} and {}; common input {}",
            self.first_rule,
            self.first_rule + 1,
            self.first.input.hex()
        )?;
        for effect in [&self.first, &self.second] {
            writeln!(
                f,
                "copy {}: native {} above {}, rewritten result {}",
                effect.copy,
                effect.operation.hex(),
                effect.parent.hex(),
                effect.output.hex()
            )?;
            if !effect.sources.is_empty() {
                writeln!(
                    f,
                    "  squashed sources: {}",
                    effect
                        .sources
                        .iter()
                        .map(|id| id.hex())
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
        }
        Ok(())
    }
}

struct Previous {
    rule: u64,
    race: Race,
    effect: Effect,
}

#[derive(Default)]
pub(super) struct Tracker {
    ordinal: u64,
    active: Option<Race>,
    previous: Option<Previous>,
    witnessed: BTreeMap<Race, Witness>,
}

impl Tracker {
    pub(super) fn rule(&mut self, name: &'static str) {
        self.ordinal += 1;
        self.active = Race::ALL.into_iter().find(|race| race.rule() == name);
        if self.active.is_none() {
            self.previous = None;
        }
    }

    /// A barrier invalidates future pairing, not a race already observed before it.
    pub(super) fn interrupt(&mut self) {
        self.previous = None;
        self.active = None;
    }

    /// Called only for a successful invocation and the first capture of its native source.
    pub(super) fn command(
        &mut self,
        op: &Operation,
        snapshot: &CommandSnapshot,
        before: &BTreeSet<SourceKey>,
    ) {
        let Some(race) = self.active else { return };
        let Some(effect) = Effect::of(race, op, snapshot) else {
            return;
        };
        if let Some(previous) = &self.previous
            && previous.rule + 1 == self.ordinal
            && previous.race == race
            && previous.effect.copy != effect.copy
            && previous.effect.input == effect.input
            && previous.effect.output != effect.output
            && previous.effect.operation != effect.operation
            && previous.effect.key != effect.key
            && !before.contains(&previous.effect.key)
            && (race != Race::ConcurrentSquashes
                || previous.effect.sources.is_disjoint(&effect.sources))
        {
            self.witnessed.entry(race).or_insert_with(|| Witness {
                first_rule: previous.rule,
                first: previous.effect.clone(),
                second: effect.clone(),
            });
        }
        self.previous = Some(Previous {
            rule: self.ordinal,
            race,
            effect,
        });
    }

    pub(super) fn witnesses(&self) -> impl Iterator<Item = (Race, &Witness)> {
        self.witnessed
            .iter()
            .map(|(&race, witness)| (race, witness))
    }
}

#[cfg(test)]
mod tests {
    use jj_lib::op_store::{View, ViewId};

    use super::*;

    fn captured(
        race: Race,
        copy: &str,
        sequence: u8,
        input: u8,
        source: Option<u8>,
    ) -> (Operation, CommandSnapshot) {
        let id = |x| CommitId::from_bytes(&[x; 20]);
        let mut op = Operation::make_root(ViewId::from_bytes(&[0; 64]));
        let parent = OperationId::from_bytes(&[sequence.wrapping_add(20); 64]);
        op.parents = vec![parent.clone()];
        op.metadata.description = format!(
            "{}{}",
            match race {
                Race::SameChangeRewritten => "describe commit ",
                Race::ConcurrentSquashes => "squash commits into ",
            },
            id(input).hex()
        );
        op.metadata.time.start.timestamp.0 = i64::from(sequence);
        op.metadata.time.end.timestamp.0 = i64::from(sequence) + 1;
        let old = std::iter::once(id(input)).chain(source.map(id)).collect();
        let predecessors = BTreeMap::from([(id(sequence), old)]);
        op.commit_predecessors = Some(predecessors.clone());
        let view = View::make_root(id(0));
        let snapshot = CommandSnapshot {
            id: OperationId::from_bytes(&[sequence; 64]),
            copy: copy.to_owned(),
            copies: BTreeSet::new(),
            parent,
            input: None,
            predecessors: Some(predecessors),
            base: view.clone(),
            made: view,
        };
        (op, snapshot)
    }

    fn record(
        tracker: &mut Tracker,
        race: Race,
        copy: &str,
        seq: u8,
        input: u8,
        source: Option<u8>,
        before: &BTreeSet<SourceKey>,
    ) {
        tracker.rule(race.rule());
        let (op, snapshot) = captured(race, copy, seq, input, source);
        tracker.command(&op, &snapshot, before);
    }

    #[test]
    fn rewrite_witness_requires_two_independent_copies_of_the_same_input() {
        let race = Race::SameChangeRewritten;
        for (copy, input, known, expected) in [
            ("beta", 9, false, 1),
            ("alpha", 9, false, 0),
            ("beta", 8, false, 0),
            ("beta", 9, true, 0),
        ] {
            let mut tracker = Tracker::default();
            record(&mut tracker, race, "alpha", 1, 9, None, &BTreeSet::new());
            assert_eq!(tracker.witnesses().count(), 0, "one action is insufficient");
            let before = if known {
                BTreeSet::from([SourceKey::of(&captured(race, "alpha", 1, 9, None).0)])
            } else {
                BTreeSet::new()
            };
            record(&mut tracker, race, copy, 2, input, None, &before);
            assert_eq!(tracker.witnesses().count(), expected);
        }
    }

    #[test]
    fn sync_history_rewrite_or_unrelated_rule_breaks_pairing() {
        for barrier in [true, false] {
            let mut tracker = Tracker::default();
            record(
                &mut tracker,
                Race::SameChangeRewritten,
                "alpha",
                1,
                9,
                None,
                &BTreeSet::new(),
            );
            if barrier {
                tracker.interrupt();
            } else {
                tracker.rule("status");
            }
            record(
                &mut tracker,
                Race::SameChangeRewritten,
                "beta",
                2,
                9,
                None,
                &BTreeSet::new(),
            );
            assert_eq!(tracker.witnesses().count(), 0);
        }
    }

    #[test]
    fn squash_witness_requires_distinct_native_contributions() {
        for source in [None, Some(7), Some(8)] {
            let mut tracker = Tracker::default();
            record(
                &mut tracker,
                Race::ConcurrentSquashes,
                "alpha",
                1,
                9,
                Some(7),
                &BTreeSet::new(),
            );
            record(
                &mut tracker,
                Race::ConcurrentSquashes,
                "beta",
                2,
                9,
                source,
                &BTreeSet::new(),
            );
            assert_eq!(tracker.witnesses().count(), usize::from(source == Some(8)));
        }
    }

    #[test]
    fn claimed_intent_noop_and_realization_are_not_native_effects() {
        for damage in [0, 1, 2, 3] {
            let mut tracker = Tracker::default();
            record(
                &mut tracker,
                Race::SameChangeRewritten,
                "alpha",
                1,
                9,
                None,
                &BTreeSet::new(),
            );
            tracker.rule("describe");
            let (mut op, mut snapshot) = captured(Race::SameChangeRewritten, "beta", 2, 9, None);
            match damage {
                0 => {
                    op.commit_predecessors = None;
                    snapshot.predecessors = None;
                }
                1 => {
                    let id = CommitId::from_bytes(&[9; 20]);
                    let p = Some(BTreeMap::from([(id.clone(), vec![id])]));
                    op.commit_predecessors = p.clone();
                    snapshot.predecessors = p;
                }
                2 => {
                    op.metadata
                        .attributes
                        .insert(CANONICAL_ATTRIBUTE.to_owned(), "realized".to_owned());
                }
                _ => {
                    snapshot.parent = OperationId::from_bytes(&[99; 64]);
                }
            }
            tracker.command(&op, &snapshot, &BTreeSet::new());
            assert_eq!(tracker.witnesses().count(), 0);
        }
    }

    /// The bridge uses real jj predecessor records and the same actor hooks as the search.
    /// No witness is inferred from the rule labels or requested arguments alone.
    #[test]
    fn captured_native_commands_witness_concurrent_rewrites_and_squashes() {
        use crate::coverage;
        use crate::world::{Naming, Setup, World};

        let _report = coverage::Report::new("native-witness-bridge");
        for race in Race::ALL {
            let mut world = World::new(Setup {
                nodes: 2,
                naming: Naming::Own,
                prejoin: false,
                secondary: false,
            });
            world.commit(0, 0, 0);
            let target = world.jj(0, &["log", "--no-graph", "-r", "@-", "-T", "commit_id"]);
            let mut sources = vec![];
            if race == Race::ConcurrentSquashes {
                for file in [1, 2] {
                    world.jj(0, &["new", &target]);
                    world.commit(0, 0, file);
                    sources
                        .push(world.jj(0, &["log", "--no-graph", "-r", "@-", "-T", "commit_id"]));
                }
            }
            world.converge();
            let case = coverage::start_case();
            let actions: Vec<Vec<&str>> = match race {
                Race::SameChangeRewritten => ["one", "two"]
                    .into_iter()
                    .map(|message| vec!["describe", target.as_str(), "-m", message])
                    .collect(),
                Race::ConcurrentSquashes => sources
                    .iter()
                    .map(|source| {
                        vec![
                            "squash",
                            "--from",
                            source.as_str(),
                            "--into",
                            target.as_str(),
                            "--use-destination-message",
                        ]
                    })
                    .collect(),
            };
            for (m, args) in actions.iter().enumerate() {
                coverage::fired(race.rule());
                world.jj(m, args);
                assert_eq!(case.witnessed(race.catalogue_name()), m == 1);
            }
            world.converge();
            case.passed();
        }
    }
}
