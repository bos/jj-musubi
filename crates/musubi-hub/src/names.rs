//! The names hives get from their remote URLs ([`RemoteUrl`]): the owner and repository on
//! a forge, as people refer to it.

pub use musubi_jj::remote_url::RemoteUrl;

/// The names a new hive could have, shortest first: from the remote named `origin`, else
/// the first remote by name, else the repository's directory. Each is a valid name
/// ([`check_name`]), made from what the user never typed as one: a URL's `%20` is a space,
/// and a space a `-`.
pub fn name_candidates(remotes: &[(String, String)], dir_name: &str) -> Vec<String> {
    let mut sorted: Vec<&(String, String)> = remotes.iter().collect();
    sorted.sort_by_key(|(name, _)| (name != "origin", name.clone()));
    let from_remote = sorted
        .iter()
        .find_map(|(_, url)| RemoteUrl::parse(url))
        .map(|url| tidy_all(url.name_candidates()))
        .filter(|names| !names.is_empty());
    from_remote.unwrap_or_else(|| {
        let names = tidy_all(vec![dir_name.to_owned()]);
        if names.is_empty() {
            vec!["hive".to_owned()]
        } else {
            names
        }
    })
}

/// `names`, [`tidy`], without any left empty or repeated.
fn tidy_all(names: Vec<String>) -> Vec<String> {
    let mut tidied: Vec<String> = names.iter().map(|name| tidy(name)).collect();
    tidied.retain(|name| !name.is_empty());
    tidied.dedup();
    tidied
}

/// `name`, percent-decoded as a URL's path is, with each run of whitespace a `-`, and without
/// other control characters, or whitespace at either end.
fn tidy(name: &str) -> String {
    let decoded = percent_decoded(name);
    let mut tidied = String::with_capacity(decoded.len());
    let mut gap = false;
    for c in decoded.chars() {
        if c.is_whitespace() {
            gap = true;
        } else if !c.is_control() {
            if gap && !tidied.is_empty() {
                tidied.push('-');
            }
            gap = false;
            tidied.push(c);
        }
    }
    tidied
}

/// `text` with each `%` and two hex digits the byte they stand for, unless that leaves it not
/// UTF-8.
fn percent_decoded(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut at = 0;
    while at < bytes.len() {
        let hex = bytes
            .get(at + 1..at + 3)
            .and_then(|hex| std::str::from_utf8(hex).ok())
            .and_then(|hex| u8::from_str_radix(hex, 16).ok());
        match hex {
            Some(byte) if bytes[at] == b'%' => {
                decoded.push(byte);
                at += 3;
            }
            _ => {
                decoded.push(bytes[at]);
                at += 1;
            }
        }
    }
    String::from_utf8(decoded).unwrap_or_else(|_| text.to_owned())
}

/// The first candidate `taken` says is free, or the last one with a number appended.
pub fn choose_name(candidates: &[String], taken: impl Fn(&str) -> bool) -> String {
    if let Some(free) = candidates.iter().find(|name| !taken(name)) {
        return free.clone();
    }
    let base = candidates.last().map_or("hive", String::as_str);
    (2..)
        .map(|n| format!("{base}-{n}"))
        .find(|name| !taken(name))
        .expect("some number is free")
}

/// Why `name` can't name a hive, if it can't.
pub fn check_name(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("a hive name can't be empty".to_owned());
    }
    if name.chars().any(char::is_whitespace) {
        return Err(format!("a hive name can't contain spaces: {name:?}"));
    }
    if name.chars().any(char::is_control) {
        return Err(format!(
            "a hive name can't contain control characters: {name:?}"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidates_shortest_first() {
        let url = RemoteUrl::parse("git@github.com:bos/jj-musubi.git").unwrap();
        assert_eq!(
            url.name_candidates(),
            ["jj-musubi", "bos/jj-musubi", "github.com/bos/jj-musubi"]
        );
        let url = RemoteUrl::parse("https://example.com/project").unwrap();
        assert_eq!(url.name_candidates(), ["project", "example.com/project"]);
    }

    #[test]
    fn names_come_from_origin_then_the_first_remote_then_the_directory() {
        let remotes = |list: &[(&str, &str)]| -> Vec<(String, String)> {
            list.iter()
                .map(|(n, u)| ((*n).to_owned(), (*u).to_owned()))
                .collect()
        };
        let both = remotes(&[
            ("upstream", "https://github.com/jj-vcs/jj"),
            ("origin", "https://github.com/bos/jj"),
        ]);
        assert_eq!(name_candidates(&both, "dir")[1], "bos/jj");
        let others = remotes(&[
            ("zz", "https://github.com/z/z"),
            ("fork", "https://github.com/bos/jj"),
        ]);
        assert_eq!(name_candidates(&others, "dir")[1], "bos/jj");
        assert_eq!(name_candidates(&[], "project"), ["project"]);
        assert_eq!(
            name_candidates(&remotes(&[("origin", " ")]), "project"),
            ["project"]
        );
    }

    /// A name the user never typed, from a remote's URL or the repository's directory, is
    /// one a hive can have: they meant `My%20Repo` and `My Repo` as `My Repo`, which a name
    /// can't contain, and a name of control characters is no name.
    #[test]
    fn default_names_are_valid() {
        let origin = |url: &str| vec![("origin".to_owned(), url.to_owned())];
        let cases = [
            (name_candidates(&[], "My Project"), "My-Project"),
            (name_candidates(&[], " My \t Project\n"), "My-Project"),
            (name_candidates(&[], "a\u{1}b"), "ab"),
            (name_candidates(&[], "\u{1}"), "hive"),
            (
                name_candidates(&origin("/srv/git/My Project.git"), "dir"),
                "My-Project",
            ),
            (
                name_candidates(&origin("https://example.com/team/My%20Repo"), "dir"),
                "My-Repo",
            ),
            // Not percent-encoding after all.
            (
                name_candidates(&origin("https://example.com/team/100%25%zz"), "dir"),
                "100%%zz",
            ),
            (
                name_candidates(&origin("https://example.com/team/%ff"), "dir"),
                "%ff",
            ),
        ];
        for (names, first) in cases {
            assert_eq!(names[0], first, "{names:?}");
            for name in &names {
                assert_eq!(check_name(name), Ok(()), "{names:?}");
            }
        }
        assert_eq!(
            name_candidates(&origin("https://example.com/team/My%20Repo"), "dir"),
            ["My-Repo", "team/My-Repo", "example.com/team/My-Repo"]
        );
    }

    /// Each refusal names what is wrong with the name.
    #[test]
    fn invalid_names_say_why() {
        assert_eq!(check_name(""), Err("a hive name can't be empty".to_owned()));
        assert_eq!(
            check_name("My Project"),
            Err(r#"a hive name can't contain spaces: "My Project""#.to_owned())
        );
        assert_eq!(
            check_name("a\u{7}b"),
            Err(r#"a hive name can't contain control characters: "a\u{7}b""#.to_owned())
        );
        assert_eq!(check_name("bos/jj-musubi"), Ok(()));
    }

    #[test]
    fn chooses_the_shortest_free_name() {
        let candidates: Vec<String> = ["jj-musubi", "bos/jj-musubi", "github.com/bos/jj-musubi"]
            .map(String::from)
            .to_vec();
        assert_eq!(choose_name(&candidates, |_| false), "jj-musubi");
        assert_eq!(
            choose_name(&candidates, |n| n == "jj-musubi"),
            "bos/jj-musubi"
        );
        assert_eq!(
            choose_name(&candidates, |n| n != "github.com/bos/jj-musubi"),
            "github.com/bos/jj-musubi"
        );
        assert_eq!(
            choose_name(&candidates, |n| !n.ends_with("-3")),
            "github.com/bos/jj-musubi-3"
        );
    }
}
