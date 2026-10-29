//! Machine identity, and how each machine's workspaces appear to the others.
//!
//! Workspaces are per-machine (docs/internals/design.md, "Per-machine state in a replicated
//! view"), but where each machine's working copies are is worth seeing. The canonical view
//! records every machine's workspaces under machine-qualified keys, `<machine>/<workspace>`. Each
//! machine shows the others' as workspaces of its own view, named after the machine, so `jj log`
//! shows beta's working copy as `beta/default@`. They are never git refs, so nothing git does can
//! touch them. jj moves them as it moves any workspace when it rewrites or abandons their
//! commits, and canonicalization takes those moves, but no other change a machine makes to
//! another machine's workspaces: adding, forgetting or renaming them stays local, and the next
//! realization shows them again. Only a forget of the whole copy, which musubi writes, removes
//! them (`crate::presence`).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::merge::SameChange;
use jj_lib::merge::trivial_merge;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::settings::JJRng;

use crate::files;

/// This machine's identity in the hive: a readable name plus a random suffix, `name#1a2b3c4d`,
/// so that two machines with the same hostname are never confused. Stored on first use,
/// because canonical operations embed it and must not change when recomputed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine {
    key: String,
}

impl Machine {
    /// The suffix comes from `rng`, jj's, which `debug.randomness-seed` makes repeatable, as
    /// it does jj's change ids: so a test that names two machines alike names them the same
    /// way every time it runs.
    pub(crate) fn load_or_create(path: &Path, default_name: &str, rng: &JJRng) -> io::Result<Self> {
        match fs::read_to_string(path) {
            Ok(key) if !key.trim().is_empty() => {
                return Ok(Self {
                    key: key.trim().to_owned(),
                });
            }
            Ok(_) => {}
            Err(err) if err.kind() == io::ErrorKind::NotFound => {}
            Err(err) => return Err(err),
        }
        let suffix = rng.new_change_id(4).hex();
        let key = format!("{}#{suffix}", sanitize(default_name));
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        files::replace(path, key.as_bytes())?;
        Ok(Self { key })
    }

    pub fn key(&self) -> &str {
        &self.key
    }

    pub fn name(&self) -> &str {
        machine_name(&self.key)
    }
}

/// A name usable as a jj remote name and a git ref component.
pub fn sanitize(name: &str) -> String {
    let cleaned: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect();
    let cleaned = cleaned.trim_matches('-').to_lowercase();
    if cleaned.is_empty() {
        "machine".to_owned()
    } else {
        cleaned
    }
}

/// The readable part of a machine key: `beta` of `beta#1a2b3c4d`.
pub fn machine_name(key: &str) -> &str {
    key.split_once('#').map_or(key, |(name, _)| name)
}

/// A machine key's suffix: `1a2b3c4d` of `beta#1a2b3c4d`.
fn suffix(key: &str) -> &str {
    key.split_once('#').map_or("", |(_, id)| id)
}

/// The start of a machine key's suffix: its first four characters, as `candidates` in
/// formal/Musubi/Names.lean. Keys come from other machines, whose `musubi/machine` may have
/// been edited by hand, so the suffix may have characters of more than one byte.
fn short_id(key: &str) -> &str {
    let id = suffix(key);
    &id[..id.char_indices().nth(4).map_or(id.len(), |(at, _)| at)]
}

/// The name under which a machine's workspaces are shown when its plain name isn't free:
/// `beta-1a2b`, the first of `candidates` after the name.
pub fn qualified_name(key: &str) -> String {
    format!("{}-{}", machine_name(key), short_id(key))
}

/// The names under which a machine's workspaces can be shown, in the order
/// [`display_names`] tries them: `name`, if `plain`; `name-1a2b`; `name-1a2b3c4d`, with the
/// whole suffix; then that with ever more dashes, so that one is free however many names are
/// taken. This is `candidates` in formal/Musubi/Names.lean.
fn candidates(key: &str, plain: bool) -> impl Iterator<Item = String> {
    let name = machine_name(key);
    let full = format!("{name}-{}", suffix(key));
    plain
        .then(|| name.to_owned())
        .into_iter()
        .chain([qualified_name(key), full.clone()])
        .chain((1..).map(move |dashes| format!("{full}{}", "-".repeat(dashes))))
}

/// Whether a machine's workspaces could be shown under `prefix`, whichever machines it is
/// shown among: whether `prefix` is one of its `candidates`. Which one it is shown under
/// changes as other machines come and go.
pub fn could_be_shown_as(key: &str, prefix: &str) -> bool {
    let name = machine_name(key);
    let full = format!("{name}-{}", suffix(key));
    prefix == name
        || prefix == qualified_name(key)
        || prefix
            .strip_prefix(full.as_str())
            .is_some_and(|dashes| dashes.chars().all(|c| c == '-'))
}

/// The canonical key of `workspace` on `machine`.
pub fn workspace_key(machine: &str, workspace: &str) -> WorkspaceNameBuf {
    WorkspaceNameBuf::from(format!("{machine}/{workspace}"))
}

/// Splits a canonical workspace key into machine key and workspace name.
pub fn split_key(key: &str) -> Option<(&str, &str)> {
    key.split_once('/')
}

/// The names under which machines' workspaces are shown, as `<name>/<workspace>`: each
/// machine, in order, takes the first of its `candidates` that no machine before it took
/// and that `taken` doesn't say is in use; its plain name only if no other machine has that
/// name. So no two machines are shown alike, nor any as a name `taken` holds: formal/Musubi/
/// Names.lean proves the names injective (`localName_injective`).
pub fn display_names(
    machines: &BTreeSet<String>,
    taken: impl Fn(&str) -> bool,
) -> BTreeMap<String, String> {
    let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
    for machine in machines {
        *by_name.entry(machine_name(machine)).or_default() += 1;
    }
    let mut used: BTreeSet<String> = BTreeSet::new();
    machines
        .iter()
        .map(|machine| {
            let plain = by_name[machine_name(machine)] == 1;
            let display = candidates(machine, plain)
                .find(|name| !used.contains(name) && !taken(name))
                .expect("a name longer than every one taken is free");
            used.insert(display.clone());
            (machine.clone(), display)
        })
        .collect()
}

/// Merges one workspace's working-copy commit three-way, as jj does when it merges
/// concurrent operations: a trivial merge where there is one, then a removal on either side,
/// then `ours`. This is jj-lib's private `MutableRepo::merge_wc_commit`, built the same way
/// on jj's `trivial_merge`; the `workspace_merge_matches_jj` test checks that the two agree.
pub fn merge_working_copy<'a>(
    ours: Option<&'a CommitId>,
    base: Option<&'a CommitId>,
    theirs: Option<&'a CommitId>,
) -> Option<&'a CommitId> {
    if let Some(resolved) = trivial_merge(&[ours, base, theirs], SameChange::Accept) {
        *resolved
    } else if ours.is_none() || theirs.is_none() {
        None
    } else {
        ours
    }
}

/// Moves working-copy commits along the rewrites an operation records: a commit rewritten
/// into several (divergent or split) is followed to the first of them.
pub fn follow_rewrites<K>(
    workspaces: &mut BTreeMap<K, CommitId>,
    predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
) {
    let Some(predecessors) = predecessors else {
        return;
    };
    let mut successors: BTreeMap<&CommitId, &CommitId> = BTreeMap::new();
    for (new, olds) in predecessors {
        for old in olds {
            successors.entry(old).or_insert(new);
        }
    }
    for wc in workspaces.values_mut() {
        // Rewrites within one operation form chains; follow them to the end.
        let mut seen = BTreeSet::new();
        while let Some(&next) = successors.get(&*wc) {
            if !seen.insert(next.clone()) {
                break;
            }
            *wc = next.clone();
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::sync::Arc;

    use jj_lib::config::ConfigLayer;
    use jj_lib::config::ConfigSource;
    use jj_lib::config::StackedConfig;
    use jj_lib::settings::UserSettings;

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    #[test]
    fn names_are_qualified_only_when_ambiguous() {
        let machines: BTreeSet<String> = [
            "beta#11112222",
            "mac#aaaa0000",
            "mac#bbbb0000",
            "git#cccc0000",
            "origin#dddd0000",
        ]
        .map(str::to_owned)
        .into();
        let names = display_names(&machines, |name| name == "origin");
        assert_eq!(names["beta#11112222"], "beta");
        assert_eq!(names["mac#aaaa0000"], "mac-aaaa");
        assert_eq!(names["mac#bbbb0000"], "mac-bbbb");
        assert_eq!(names["git#cccc0000"], "git");
        assert_eq!(names["origin#dddd0000"], "origin-dddd");
    }

    /// Where the start of a suffix doesn't tell two machines apart, or a machine's name is
    /// another's longer one, the later machine takes a longer name: the cases in
    /// formal/Musubi/Names.lean.
    #[test]
    fn longer_names_where_shorter_clash() {
        let machines: BTreeSet<String> = ["mac#aaaa1111", "mac#aaaa2222"].map(str::to_owned).into();
        let names = display_names(&machines, |_| false);
        assert_eq!(names["mac#aaaa1111"], "mac-aaaa");
        assert_eq!(names["mac#aaaa2222"], "mac-aaaa2222");
        let machines: BTreeSet<String> = ["mac#aaaa0000", "mac#bbbb0000", "mac-aaaa#12345678"]
            .map(str::to_owned)
            .into();
        let names = display_names(&machines, |_| false);
        assert_eq!(names["mac#aaaa0000"], "mac-aaaa");
        assert_eq!(names["mac-aaaa#12345678"], "mac-aaaa-1234");
        let machines: BTreeSet<String> = ["beta#1a2b3c4d"].map(str::to_owned).into();
        let own = ["beta/x", "beta-1a2b/default"];
        let names = display_names(&machines, |prefix| {
            own.iter().any(|w| w.starts_with(&format!("{prefix}/")))
        });
        assert_eq!(names["beta#1a2b3c4d"], "beta-1a2b3c4d");
    }

    /// `display_names` against `assign` in formal/Musubi/Names.lean: each machine, in order,
    /// is shown under the first of its candidates that no machine before it took and that
    /// starts no name of this machine's own, and so the names here of a view's workspaces are
    /// distinct (`localName_injective`). Names and suffixes are drawn from few, so that they
    /// clash.
    #[hegel::test(test_cases = 300)]
    fn local_names_are_distinct(tc: TestCase) {
        const NAMES: [&str; 3] = ["mac", "mac-aaaa", "mac-aaaa1111"];
        const SUFFIXES: [&str; 4] = ["aaaa1111", "aaaa2222", "bbbb0000", "aaaa"];
        const OWN: [&str; 7] = [
            "default",
            "mac/x",
            "mac-aaaa/default",
            "mac-aaaa2222/default",
            "mac-aaaa1111-/x",
            "mac-aaaa1111/default",
            "mac-aaaa-aaaa/x",
        ];
        let pick = |n: usize| tc.draw(gs::integers::<usize>().max_value(n - 1));
        let machines: BTreeSet<String> = (0..pick(5))
            .map(|_| {
                format!(
                    "{}#{}",
                    NAMES[pick(NAMES.len())],
                    SUFFIXES[pick(SUFFIXES.len())]
                )
            })
            .collect();
        let own: BTreeSet<&str> = (0..pick(4)).map(|_| OWN[pick(OWN.len())]).collect();
        let taken = |prefix: &str| own.iter().any(|w| w.starts_with(&format!("{prefix}/")));
        let names = display_names(&machines, taken);

        let mut used = BTreeSet::new();
        for machine in &machines {
            let plain = machines
                .iter()
                .filter(|other| machine_name(other) == machine_name(machine))
                .count()
                == 1;
            let shown = &names[machine];
            // `candidates` in formal/Musubi/Names.lean, spelled out here.
            let (name, suffix) = machine.split_once('#').unwrap();
            let full = format!("{name}-{suffix}");
            let earlier: Vec<String> = plain
                .then(|| name.to_owned())
                .into_iter()
                .chain([format!("{name}-{}", &suffix[..4]), full.clone()])
                .chain((1..).map(|dashes| format!("{full}{}", "-".repeat(dashes))))
                .take_while(|candidate| candidate != shown)
                .take(64)
                .collect();
            assert!(
                earlier.len() < 64,
                "{machine} is shown as {shown}, not a candidate"
            );
            for candidate in &earlier {
                assert!(
                    used.contains(candidate) || taken(candidate),
                    "{candidate} was free"
                );
            }
            assert!(
                !taken(shown) && used.insert(shown.clone()),
                "{shown} wasn't free"
            );
        }

        let mut local: BTreeSet<String> = own.iter().map(|w| (*w).to_owned()).collect();
        for workspace in ["default", "x"] {
            for shown in names.values() {
                assert!(
                    local.insert(format!("{shown}/{workspace}")),
                    "{names:?}, {own:?}"
                );
            }
        }
    }

    /// A suffix edited by hand to have characters of more than one byte is cut after four
    /// characters, not four bytes.
    #[test]
    fn names_qualify_with_any_suffix() {
        let machines: BTreeSet<String> = ["mac#abcéf", "mac#ü"].map(str::to_owned).into();
        let names = display_names(&machines, |_| false);
        assert_eq!(names["mac#abcéf"], "mac-abcé");
        assert_eq!(names["mac#ü"], "mac-ü");
    }

    /// jj's RNG, as `debug.randomness-seed = seed` makes it.
    fn rng(seed: u64) -> Arc<JJRng> {
        let mut config = StackedConfig::with_defaults();
        let text = format!("debug.randomness-seed = {seed}");
        config.add_layer(ConfigLayer::parse(ConfigSource::User, &text).unwrap());
        UserSettings::from_config_and_home_dir(config, None)
            .unwrap()
            .get_rng()
    }

    #[test]
    fn identity_is_kept() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("machine");
        let first = Machine::load_or_create(&path, "Bryan's MacBook Pro", &rng(1)).unwrap();
        assert!(
            first.key().starts_with("bryan-s-macbook-pro#"),
            "{}",
            first.key()
        );
        let again = Machine::load_or_create(&path, "something else", &rng(2)).unwrap();
        assert_eq!(first, again);
    }

    /// The e2e search replays a case with machines named alike only if their suffixes come
    /// out the same again.
    #[test]
    fn a_seed_repeats_the_suffix() {
        let dir = tempfile::tempdir().unwrap();
        let key = |file: &str, seed| {
            let path = dir.path().join(file);
            Machine::load_or_create(&path, "mac", &rng(seed))
                .unwrap()
                .key
        };
        assert_eq!(key("a", 1), key("b", 1));
        assert_ne!(key("c", 1), key("d", 2));
    }
}
