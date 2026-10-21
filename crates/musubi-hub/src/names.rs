//! The names hives get from their remote URLs ([`RemoteUrl`]): the owner and repository on
//! a forge, as people refer to it.

pub use musubi_jj::remote_url::RemoteUrl;

/// The names a new hive could have, shortest first: from the remote named `origin`, else
/// the first remote by name, else the repository's directory.
pub fn name_candidates(remotes: &[(String, String)], dir_name: &str) -> Vec<String> {
    let mut sorted: Vec<&(String, String)> = remotes.iter().collect();
    sorted.sort_by_key(|(name, _)| (name != "origin", name.clone()));
    let from_remote = sorted
        .iter()
        .find_map(|(_, url)| RemoteUrl::parse(url))
        .map(|url| url.name_candidates())
        .filter(|names| !names.is_empty());
    from_remote.unwrap_or_else(|| {
        let name = dir_name.trim();
        vec![if name.is_empty() { "hive" } else { name }.to_owned()]
    })
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
    if name.chars().any(|c| c.is_whitespace() || c.is_control()) {
        return Err(format!("a hive name can't contain spaces: {name:?}"));
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
