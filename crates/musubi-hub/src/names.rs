//! Remote URLs as a hub compares them, and the names hives get from them.
//!
//! Two clones of one repository often name its remote differently: one over https, one over
//! ssh, one with `.git` and one without. [`RemoteUrl::parse`] reduces each form to a host
//! and a path, and [`RemoteUrl::key`] is what the hub matches. A hive's name comes from
//! the same parse: the owner and repository on a forge, as people refer to it.

/// A remote URL reduced to what identifies the repository it points to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemoteUrl {
    /// Lowercase, without any user, and with the port only when it isn't the scheme's
    /// default. Empty for a repository on this machine's filesystem.
    pub host: String,
    /// The repository's path on the host, without leading or trailing `/` or a `.git`
    /// suffix. A local path keeps its leading `/`.
    pub path: String,
}

impl RemoteUrl {
    /// Parses the URL forms git accepts: `scheme://[user@]host[:port]/path` (https, http,
    /// ssh, git), scp-style `[user@]host:path`, `file://path`, and local paths.
    pub fn parse(url: &str) -> Option<Self> {
        let url = url.trim();
        if url.is_empty() {
            return None;
        }
        let parsed = if let Some((scheme, rest)) = url.split_once("://") {
            let scheme = scheme.to_ascii_lowercase();
            if scheme == "file" {
                // `file:///srv/repo`, or `file://localhost/srv/repo`.
                let path = rest.strip_prefix("localhost").unwrap_or(rest);
                Self::local(path)
            } else {
                let (authority, path) = rest.split_once('/').unwrap_or((rest, ""));
                let host = host_of(authority, default_port(&scheme))?;
                Self::remote(host, path)
            }
        } else if let Some((authority, path)) = scp_like(url) {
            Self::remote(host_of(authority, None)?, path)
        } else {
            Self::local(url)
        };
        (!parsed.path.is_empty() || !parsed.host.is_empty()).then(|| parsed.canonical_forge())
    }

    fn remote(host: String, path: &str) -> Self {
        Self {
            host,
            path: clean_path(path).trim_start_matches('/').to_owned(),
        }
    }

    fn local(path: &str) -> Self {
        Self {
            host: String::new(),
            path: clean_path(&path.replace('\\', "/")),
        }
    }

    /// Azure DevOps spells one repository three ways; make them one.
    fn canonical_forge(self) -> Self {
        let parts: Vec<&str> = self.path.split('/').collect();
        let azure = |path: String| Self {
            host: "dev.azure.com".to_owned(),
            path,
        };
        match (self.host.as_str(), parts.as_slice()) {
            ("dev.azure.com", [org, project, "_git", repo]) => {
                azure(format!("{org}/{project}/{repo}"))
            }
            ("ssh.dev.azure.com" | "vs-ssh.visualstudio.com", ["v3", org, project, repo]) => {
                azure(format!("{org}/{project}/{repo}"))
            }
            (host, [project, "_git", repo]) if host.ends_with(".visualstudio.com") => {
                let org = host.trim_end_matches(".visualstudio.com");
                azure(format!("{org}/{project}/{repo}"))
            }
            _ => self,
        }
    }

    /// What two URLs for the same repository have in common.
    pub fn key(&self) -> String {
        if self.host.is_empty() {
            self.path.clone()
        } else if self.path.is_empty() {
            self.host.clone()
        } else {
            format!("{}/{}", self.host, self.path)
        }
    }

    /// The repository's name as its forge shows it: `owner/repo` on GitHub and its kind,
    /// the full group path on GitLab, `org/project/repo` on Azure DevOps, and otherwise the
    /// last two components of the path.
    pub fn forge_name(&self) -> String {
        let host = self.host.as_str();
        let parts: Vec<&str> = self.path.split('/').filter(|p| !p.is_empty()).collect();
        let joined = |parts: &[&str]| parts.join("/");
        let last_two = |parts: &[&str]| joined(&parts[parts.len().saturating_sub(2)..]);
        if host == "gitlab.com" || host.starts_with("gitlab.") || host == "dev.azure.com" {
            joined(&parts)
        } else if host == "sr.ht" || host.ends_with(".sr.ht") {
            let parts: Vec<&str> = parts.iter().map(|p| p.trim_start_matches('~')).collect();
            last_two(&parts)
        } else if host.contains("gerrit") || host.ends_with(".googlesource.com") {
            // Gerrit serves authenticated https under `a/`; project names can nest.
            let parts = parts.strip_prefix(&["a"]).unwrap_or(&parts);
            joined(parts)
        } else if matches!(
            host,
            "github.com" | "codeberg.org" | "bitbucket.org" | "gitea.com"
        ) || host.contains("forgejo")
            || host.contains("gitea")
        {
            joined(&parts[..parts.len().min(2)])
        } else {
            last_two(&parts)
        }
    }

    /// The names a hive with this remote could have, shortest first: the repository's name,
    /// its forge name, and the forge name with the host.
    pub fn name_candidates(&self) -> Vec<String> {
        let forge = self.forge_name();
        let short = forge.rsplit('/').next().unwrap_or(&forge).to_owned();
        let mut names = vec![short, forge.clone()];
        if !self.host.is_empty() {
            names.push(format!("{}/{forge}", self.host));
        }
        names.dedup();
        names.retain(|name| !name.is_empty());
        names
    }
}

/// `host` from `[user@]host[:port]`, lowercase, dropping the user and a default port.
fn host_of(authority: &str, default_port: Option<&str>) -> Option<String> {
    let host = authority
        .rsplit_once('@')
        .map_or(authority, |(_, host)| host);
    let host = host.to_ascii_lowercase();
    // A bracketed IPv6 address has colons of its own.
    let port_at = match host.rfind(']') {
        Some(end) => host[end..].find(':').map(|i| end + i),
        None => host.rfind(':'),
    };
    let host = match port_at {
        Some(i) if Some(&host[i + 1..]) == default_port || host[i + 1..].is_empty() => {
            host[..i].to_owned()
        }
        _ => host,
    };
    (!host.is_empty()).then_some(host)
}

fn default_port(scheme: &str) -> Option<&'static str> {
    match scheme {
        "https" => Some("443"),
        "http" => Some("80"),
        "ssh" | "git+ssh" | "ssh+git" => Some("22"),
        "git" => Some("9418"),
        _ => None,
    }
}

/// Splits git's scp-like syntax, `[user@]host:path`, as git recognizes it: a colon before
/// any slash, and not a Windows drive letter.
fn scp_like(url: &str) -> Option<(&str, &str)> {
    let (authority, path) = url.split_once(':')?;
    let drive = authority.len() == 1 && authority.chars().all(|c| c.is_ascii_alphabetic());
    (!authority.is_empty() && !authority.contains('/') && !drive).then_some((authority, path))
}

/// Collapses repeated slashes and drops trailing slashes and a `.git` suffix.
fn clean_path(path: &str) -> String {
    let mut cleaned = String::with_capacity(path.len());
    for c in path.chars() {
        if !(c == '/' && cleaned.ends_with('/')) {
            cleaned.push(c);
        }
    }
    let mut cleaned = cleaned.trim_end_matches('/');
    cleaned = cleaned.strip_suffix(".git").unwrap_or(cleaned);
    cleaned.trim_end_matches('/').to_owned()
}

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

    fn key(url: &str) -> String {
        RemoteUrl::parse(url)
            .unwrap_or_else(|| panic!("{url} did not parse"))
            .key()
    }

    fn name(url: &str) -> String {
        RemoteUrl::parse(url).unwrap().forge_name()
    }

    #[test]
    fn one_repository_one_key() {
        let forms = [
            "https://github.com/bos/jj-musubi",
            "https://github.com/bos/jj-musubi.git",
            "https://github.com/bos/jj-musubi/",
            "https://bos@GitHub.com/bos/jj-musubi.git",
            "https://github.com:443/bos/jj-musubi",
            "http://github.com:80/bos/jj-musubi",
            "ssh://git@github.com/bos/jj-musubi.git",
            "ssh://git@github.com:22/bos/jj-musubi",
            "git+ssh://git@github.com/bos/jj-musubi",
            "git://github.com/bos/jj-musubi.git",
            "git@github.com:bos/jj-musubi.git",
            "github.com:bos/jj-musubi",
            "git@github.com:/bos//jj-musubi.git/",
        ];
        for form in forms {
            assert_eq!(key(form), "github.com/bos/jj-musubi", "{form}");
        }
    }

    #[test]
    fn keeps_what_distinguishes() {
        assert_eq!(
            key("https://example.com:8443/repo"),
            "example.com:8443/repo"
        );
        assert_eq!(
            key("ssh://git@example.com:2222/repo"),
            "example.com:2222/repo"
        );
        assert_ne!(
            key("https://github.com/bos/a"),
            key("https://github.com/bos/b")
        );
        assert_eq!(key("ssh://git@[::1]:22/repo"), "[::1]/repo");
        assert_eq!(key("ssh://git@[::1]:2222/repo"), "[::1]:2222/repo");
    }

    #[test]
    fn local_paths() {
        assert_eq!(key("/srv/git/project.git"), "/srv/git/project");
        assert_eq!(key("file:///srv/git/project.git/"), "/srv/git/project");
        assert_eq!(key("file://localhost/srv/git/project"), "/srv/git/project");
        assert_eq!(key(r"C:\src\project"), "C:/src/project");
        assert_eq!(key("C:/src/project.git"), "C:/src/project");
        assert_eq!(name("/srv/git/project.git"), "git/project");
        assert!(RemoteUrl::parse("  ").is_none());
    }

    #[test]
    fn forge_names() {
        let cases = [
            ("https://github.com/bos/jj-musubi.git", "bos/jj-musubi"),
            ("git@codeberg.org:forgejo/forgejo.git", "forgejo/forgejo"),
            ("https://gitea.com/gitea/tea", "gitea/tea"),
            ("https://forgejo.example.org/team/tool", "team/tool"),
            (
                "git@bitbucket.org:atlassian/python-bitbucket.git",
                "atlassian/python-bitbucket",
            ),
            ("https://gitlab.com/gitlab-org/cli.git", "gitlab-org/cli"),
            (
                "git@gitlab.com:group/subgroup/deeper/project.git",
                "group/subgroup/deeper/project",
            ),
            ("https://gitlab.example.com/a/b/c", "a/b/c"),
            ("https://git.sr.ht/~sircmpwn/hare", "sircmpwn/hare"),
            ("git@git.sr.ht:~sircmpwn/hare", "sircmpwn/hare"),
            (
                "https://dev.azure.com/contoso/Fabrikam/_git/Fabrikam",
                "contoso/Fabrikam/Fabrikam",
            ),
            (
                "https://contoso@dev.azure.com/contoso/Fabrikam/_git/Fabrikam",
                "contoso/Fabrikam/Fabrikam",
            ),
            (
                "git@ssh.dev.azure.com:v3/contoso/Fabrikam/Fabrikam",
                "contoso/Fabrikam/Fabrikam",
            ),
            (
                "https://contoso.visualstudio.com/Fabrikam/_git/Fabrikam",
                "contoso/Fabrikam/Fabrikam",
            ),
            (
                "https://gerrit.example.com/a/platform/build",
                "platform/build",
            ),
            (
                "https://android.googlesource.com/platform/build",
                "platform/build",
            ),
            ("https://example.com/git/team/project.git", "team/project"),
            ("https://example.com/project", "project"),
        ];
        for (url, expected) in cases {
            assert_eq!(name(url), expected, "{url}");
        }
        // The forms of an Azure DevOps repository match each other.
        assert_eq!(
            key("git@ssh.dev.azure.com:v3/contoso/Fabrikam/Fabrikam"),
            key("https://dev.azure.com/contoso/Fabrikam/_git/Fabrikam")
        );
    }

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
