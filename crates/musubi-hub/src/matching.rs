//! Which hive a joining repository belongs to.
//!
//! A repository is *related* to a hive when they share history: a root commit, or a commit
//! one of the repository's remote bookmarks points to. Among related hives, a remote URL in
//! common decides, so that a fork with history in common but a remote of its own isn't
//! mistaken for the original. Joining never starts a hive: when nothing matches, the joiner
//! is told so, and `musubi create` starts one.

use std::collections::BTreeSet;

/// A hive, as far as matching cares.
#[derive(Clone, Debug)]
pub struct Candidate {
    pub id: String,
    pub name: String,
    /// Whether it shares history with the joining repository (and has its backend).
    pub related: bool,
    /// Keys ([`crate::names::RemoteUrl::key`]) of every URL it has had.
    pub url_keys: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Join the hive with this id; the reason is for telling the user.
    Join {
        id: String,
        reason: String,
    },
    Create,
    Refuse(String),
    /// Several hives match, as this says.
    Ambiguous(String),
}

/// What the joining repository asked for and has.
#[derive(Clone, Debug, Default)]
pub struct Joiner {
    /// Whether it has any commit of its own.
    pub has_commits: bool,
    /// The id of the hive it asked to join.
    pub chosen: Option<String>,
    /// Whether it asked for a new hive (`musubi create`).
    pub create: bool,
    /// Whether it named the new hive itself.
    pub named: bool,
    /// Its remotes' names and URL keys.
    pub remotes: Vec<(String, String)>,
}

pub fn decide(joiner: &Joiner, hives: &[Candidate]) -> Decision {
    if !joiner.has_commits {
        return Decision::Refuse(
            "this repository has no commits to share yet; commit something first".to_owned(),
        );
    }
    if joiner.create {
        // Unless named, a new hive for a repository that would join one is most likely a
        // second copy run through `create` by mistake, which would sync with nothing.
        return match find(joiner, hives) {
            Decision::Join { id, reason } if !joiner.named => {
                let name = hives
                    .iter()
                    .find(|hive| hive.id == id)
                    .map_or(id.as_str(), |hive| hive.name.as_str());
                Decision::Refuse(format!(
                    "this repository belongs in hive {name} ({reason}); `musubi join` joins \
                     it, and `musubi create <name>` starts another hive anyway"
                ))
            }
            Decision::Ambiguous(message) if !joiner.named => Decision::Ambiguous(message),
            _ => Decision::Create,
        };
    }
    find(joiner, hives)
}

/// The hive a repository that didn't ask for a new one joins, or why it joins none.
fn find(joiner: &Joiner, hives: &[Candidate]) -> Decision {
    if let Some(chosen) = &joiner.chosen {
        let Some(hive) = hives.iter().find(|hive| &hive.id == chosen) else {
            return Decision::Refuse(format!("no hive {chosen}"));
        };
        return if hive.related {
            Decision::Join {
                id: hive.id.clone(),
                reason: "as asked".to_owned(),
            }
        } else {
            Decision::Refuse(format!(
                "this repository shares no history with hive {}; `musubi create` starts a \
                 hive of its own",
                hive.name
            ))
        };
    }
    let related: Vec<&Candidate> = hives.iter().filter(|hive| hive.related).collect();
    if related.is_empty() {
        return Decision::Refuse(
            "no hive on this hub shares history with this repository; `musubi create` starts \
             one"
            .to_owned(),
        );
    }
    if joiner.remotes.is_empty() {
        return match related.as_slice() {
            [hive] => Decision::Join {
                id: hive.id.clone(),
                reason: "matched commits".to_owned(),
            },
            several => ambiguous(several),
        };
    }
    let sharing: Vec<(&Candidate, &str)> = related
        .iter()
        .filter_map(|hive| {
            // The first of the joiner's remotes it shares, preferring `origin`.
            let mut shared: Vec<&str> = joiner
                .remotes
                .iter()
                .filter(|(_, key)| hive.url_keys.contains(key))
                .map(|(name, _)| name.as_str())
                .collect();
            shared.sort_by_key(|name| (*name != "origin", *name));
            shared.first().map(|name| (*hive, *name))
        })
        .collect();
    match sharing.as_slice() {
        [(hive, remote)] => Decision::Join {
            id: hive.id.clone(),
            reason: format!("matched remote {remote}"),
        },
        [] => match related.as_slice() {
            // A hive started from a copy that had no remotes yet.
            [hive] if hive.url_keys.is_empty() => Decision::Join {
                id: hive.id.clone(),
                reason: "matched commits".to_owned(),
            },
            // A fork, perhaps, or the same repository under a URL that doesn't look it.
            _ => {
                let mut names: Vec<&str> = related.iter().map(|hive| hive.name.as_str()).collect();
                names.sort_unstable();
                Decision::Refuse(format!(
                    "{} {} history with this repository, but not a remote; `musubi join \
                     --hive <name>` joins one anyway, and `musubi create` starts a new hive",
                    match names.as_slice() {
                        [name] => format!("hive {name}"),
                        names => format!("hives {}", names.join(", ")),
                    },
                    if names.len() == 1 { "shares" } else { "share" },
                ))
            }
        },
        several => ambiguous(&several.iter().map(|(hive, _)| *hive).collect::<Vec<_>>()),
    }
}

fn ambiguous(hives: &[&Candidate]) -> Decision {
    let mut names: Vec<&str> = hives.iter().map(|hive| hive.name.as_str()).collect();
    names.sort_unstable();
    Decision::Ambiguous(format!(
        "this repository matches several hives: {}; choose one with `musubi join --hive \
         <name>`, or start another with `musubi create <name>`",
        names.join(", ")
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hive(id: &str, related: bool, urls: &[&str]) -> Candidate {
        Candidate {
            id: id.to_owned(),
            name: format!("name-{id}"),
            related,
            url_keys: urls.iter().map(|u| (*u).to_owned()).collect(),
        }
    }

    fn joiner(remotes: &[(&str, &str)]) -> Joiner {
        Joiner {
            has_commits: true,
            remotes: remotes
                .iter()
                .map(|(n, k)| ((*n).to_owned(), (*k).to_owned()))
                .collect(),
            ..Joiner::default()
        }
    }

    fn joins(decision: &Decision) -> Option<(&str, &str)> {
        match decision {
            Decision::Join { id, reason } => Some((id, reason)),
            _ => None,
        }
    }

    const ORIGIN: (&str, &str) = ("origin", "github.com/bos/jj-musubi");

    #[test]
    fn refuses_an_empty_repository() {
        let mut empty = joiner(&[ORIGIN]);
        empty.has_commits = false;
        let hives = [hive("a", true, &[ORIGIN.1])];
        assert!(matches!(decide(&empty, &hives), Decision::Refuse(m) if m.contains("commit")));
        empty.create = true;
        assert!(matches!(decide(&empty, &hives), Decision::Refuse(_)));
    }

    fn refuses(decision: &Decision, part: &str) -> bool {
        matches!(decision, Decision::Refuse(message) if message.contains(part))
    }

    #[test]
    fn joining_never_creates_a_hive() {
        assert!(refuses(&decide(&joiner(&[ORIGIN]), &[]), "musubi create"));
        assert!(refuses(&decide(&joiner(&[]), &[]), "musubi create"));
    }

    #[test]
    fn related_hive_with_a_shared_remote_is_joined() {
        let hives = [
            hive("a", false, &[ORIGIN.1]),
            hive("b", true, &[ORIGIN.1, "example.com/other"]),
            hive("c", true, &["github.com/someone/fork"]),
        ];
        let decision = decide(&joiner(&[ORIGIN]), &hives);
        assert_eq!(joins(&decision), Some(("b", "matched remote origin")));
        // Any remote counts, not only origin; origin is named when several match.
        let decision = decide(
            &joiner(&[("upstream", "example.com/other"), ORIGIN]),
            &hives,
        );
        assert_eq!(joins(&decision), Some(("b", "matched remote origin")));
        let decision = decide(&joiner(&[("mine", "example.com/other")]), &hives);
        assert_eq!(joins(&decision), Some(("b", "matched remote mine")));
    }

    #[test]
    fn unrelated_hives_never_match_on_urls_alone() {
        let hives = [hive("a", false, &[ORIGIN.1])];
        assert!(refuses(&decide(&joiner(&[ORIGIN]), &hives), "no hive"));
    }

    #[test]
    fn a_fork_is_not_taken_for_the_original() {
        let hives = [hive("a", true, &[ORIGIN.1])];
        let fork = joiner(&[("origin", "github.com/someone/jj-musubi")]);
        let decision = decide(&fork, &hives);
        assert!(
            refuses(&decision, "hive name-a shares history"),
            "{decision:?}"
        );
        assert!(refuses(&decision, "--hive"), "{decision:?}");
        assert!(refuses(&decision, "musubi create"), "{decision:?}");
    }

    #[test]
    fn several_matches_are_refused() {
        let hives = [hive("a", true, &[ORIGIN.1]), hive("b", true, &[ORIGIN.1])];
        let Decision::Ambiguous(message) = decide(&joiner(&[ORIGIN]), &hives) else {
            panic!("expected a refusal");
        };
        assert!(message.contains("name-a, name-b"), "{message}");
        assert!(message.contains("--hive"), "{message}");
        let no_remotes = [hive("a", true, &[]), hive("b", true, &[])];
        assert!(matches!(
            decide(&joiner(&[]), &no_remotes),
            Decision::Ambiguous(_)
        ));
        // Creating another, unnamed, would only add to the confusion.
        let mut creating = joiner(&[ORIGIN]);
        creating.create = true;
        assert!(matches!(decide(&creating, &hives), Decision::Ambiguous(_)));
        creating.named = true;
        assert_eq!(decide(&creating, &hives), Decision::Create);
    }

    #[test]
    fn repositories_without_remotes() {
        // A repository without remotes joins its one related hive, remotes or not.
        let hives = [hive("a", true, &[ORIGIN.1]), hive("b", false, &[])];
        assert_eq!(
            joins(&decide(&joiner(&[]), &hives)),
            Some(("a", "matched commits"))
        );
        // One with remotes joins a single related hive that has none.
        let hives = [hive("a", true, &[])];
        assert_eq!(
            joins(&decide(&joiner(&[ORIGIN]), &hives)),
            Some(("a", "matched commits"))
        );
        // But not when another related hive is there too.
        let hives = [hive("a", true, &[]), hive("b", true, &["example.com/x"])];
        assert!(refuses(
            &decide(&joiner(&[ORIGIN]), &hives),
            "hives name-a, name-b share history"
        ));
    }

    #[test]
    fn asking_for_a_hive() {
        let hives = [hive("a", true, &[]), hive("b", false, &[ORIGIN.1])];
        let mut asking = joiner(&[ORIGIN]);
        asking.chosen = Some("a".to_owned());
        assert_eq!(joins(&decide(&asking, &hives)), Some(("a", "as asked")));
        asking.chosen = Some("b".to_owned());
        assert!(refuses(&decide(&asking, &hives), "musubi create"));
    }

    #[test]
    fn asking_for_a_new_hive() {
        let hives = [hive("a", true, &[ORIGIN.1])];
        let mut asking = joiner(&[ORIGIN]);
        asking.create = true;
        let decision = decide(&asking, &hives);
        assert!(
            refuses(&decision, "belongs in hive name-a (matched remote origin)"),
            "{decision:?}"
        );
        assert!(refuses(&decision, "musubi join"), "{decision:?}");
        asking.named = true;
        assert_eq!(decide(&asking, &hives), Decision::Create);
        // Nothing to join, or only a fork's hive: created.
        let mut fork = joiner(&[("origin", "github.com/someone/jj-musubi")]);
        fork.create = true;
        assert_eq!(decide(&fork, &hives), Decision::Create);
        assert_eq!(decide(&fork, &[]), Decision::Create);
    }
}
