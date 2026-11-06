//! Git configuration inherited by a prospective clone, read before its directory exists.

use std::collections::BTreeMap;
use std::path::Path;

use gix::config::File;
use gix::config::Source;
use gix::config::file::Metadata;
use gix::config::file::init;

use crate::remote_url::JoinRemotes;
use crate::remote_url::Remote;
use crate::remote_url::without_credentials;

/// Reads the system and user Git configuration for a new colocated copy.
/// Conditional includes use its prospective Git directory, not the caller's repository.
/// No files or directories are created.
pub fn read(git_dir: &Path) -> Result<JoinRemotes, String> {
    let git_dir = std::path::absolute(git_dir).map_err(|err| err.to_string())?;
    let home = gix::path::env::home_dir();
    let paths: Vec<Metadata> = [
        Source::GitInstallation,
        Source::System,
        Source::Git,
        Source::User,
    ]
    .into_iter()
    .filter_map(|source| {
        let path = source.storage_location(&mut |name| std::env::var_os(name))?;
        path.is_file().then(|| Metadata::from(source).at(path))
    })
    .collect();
    let load = |branch: &str| -> Result<File, String> {
        let branch = gix::refs::FullName::try_from(format!("refs/heads/{branch}"))
            .map_err(|err| err.to_string())?;
        let options = init::Options {
            includes: gix::config::file::includes::Options::follow(
                gix::config::path::interpolate::Context {
                    home_dir: home.as_deref(),
                    git_install_dir: gix::path::env::installation_config_prefix(),
                    home_for_user: Some(gix::config::path::interpolate::home_for_user),
                },
                gix::config::file::includes::conditional::Context {
                    git_dir: Some(&git_dir),
                    branch_name: Some(branch.as_ref()),
                },
            ),
            ..Default::default()
        };
        // Git commands and jj init run without repository-scoped GIT_CONFIG_COUNT and
        // GIT_CONFIG_PARAMETERS overrides (git_command::REPOSITORY_ENV).
        Ok(File::from_paths_metadata(paths.iter().cloned(), options)
            .map_err(|err| format!("{err:#}"))?
            .unwrap_or_default())
    };
    // jj initializes Git with gix: HEAD starts at main, then init.defaultBranch can
    // select another unborn branch. Resolve onbranch includes for the resulting HEAD.
    let initial = load("main")?;
    let branch = initial.string("init.defaultBranch");
    let branch = branch.as_ref().map(|value| String::from_utf8_lossy(value));
    let config = match branch.as_deref() {
        Some(branch) if branch != "main" => load(branch)?,
        _ => initial,
    };
    Ok(from_config(&config))
}

fn from_config(config: &File) -> JoinRemotes {
    let mut urls = BTreeMap::<String, (Vec<String>, Vec<String>)>::new();
    for section in config.sections_by_name("remote").into_iter().flatten() {
        let Some(name) = section.header().subsection_name() else {
            continue;
        };
        let entry = urls
            .entry(String::from_utf8_lossy(name).into_owned())
            .or_default();
        entry.0.extend(
            section
                .values("url")
                .into_iter()
                .map(|url| String::from_utf8_lossy(&url).into_owned()),
        );
        entry.1.extend(
            section
                .values("pushurl")
                .into_iter()
                .map(|url| String::from_utf8_lossy(&url).into_owned()),
        );
    }
    let remotes = urls
        .into_iter()
        .map(|(name, (urls, pushes))| {
            let fetch = urls.first();
            let expanded = fetch.and_then(|url| rewrite(config, url, "insteadOf"));
            let explicit_push = !pushes.is_empty();
            let pushes = if explicit_push { pushes } else { urls.clone() };
            let push_urls = pushes
                .into_iter()
                .map(|url| {
                    // Explicit pushurl uses insteadOf; fallback URL uses pushInsteadOf first.
                    let rewritten = (!explicit_push)
                        .then(|| rewrite(config, &url, "pushInsteadOf"))
                        .flatten()
                        .or_else(|| rewrite(config, &url, "insteadOf"))
                        .unwrap_or(url);
                    without_credentials(&rewritten)
                })
                .collect();
            (
                name,
                Remote {
                    url: fetch.map(|url| without_credentials(url)),
                    expanded_url: expanded.map(|url| without_credentials(&url)),
                    push_urls,
                },
            )
        })
        .collect();
    JoinRemotes::from_remotes(&remotes)
}

/// Git rewrites once, using the longest matching prefix; the first wins a tie.
fn rewrite(config: &File, url: &str, key: &str) -> Option<String> {
    let mut best = None::<(usize, String)>;
    for section in config.sections_by_name("url").into_iter().flatten() {
        let Some(base) = section.header().subsection_name() else {
            continue;
        };
        for prefix in section.values(key) {
            let prefix = String::from_utf8_lossy(&prefix);
            if url.starts_with(prefix.as_ref())
                && best.as_ref().is_none_or(|(len, _)| prefix.len() > *len)
            {
                best = Some((
                    prefix.len(),
                    format!("{}{}", String::from_utf8_lossy(base), &url[prefix.len()..]),
                ));
            }
        }
    }
    best.map(|(_, url)| url)
}

#[cfg(test)]
mod tests {
    use std::io::Write as _;

    use super::*;

    /// Preview expansion agrees with Git, including longest-prefix and tie rules,
    /// multiple push URLs, pushInsteadOf fallbacks, explicit pushes, and credentials.
    #[test]
    fn inherited_destinations_match_git() {
        let env = musubi_testutil::TestEnv::new();
        let repo = env.init_repo("preview");
        let text = r#"
[url "https://example.com/"]
    insteadOf = short:
[url "https://wrong.example/"]
    insteadOf = short:
[url "ssh://git@long.example/"]
    insteadOf = short:long/
[url "ssh://git@push.example/"]
    pushInsteadOf = short:
[remote "inherited.name"]
    url = short:long/repo
    url = short:other
[remote "explicit"]
    url = short:repo
    pushurl = short:push1
    pushurl = short:push2
[remote "credentials"]
    url = https://user:secret@example.org/repo.git
[remote "push-only"]
    pushurl = short:mirror
"#;
        let mut bytes = text.as_bytes().to_vec();
        let config =
            File::from_bytes_owned(&mut bytes, Metadata::from(Source::Api), Default::default())
                .unwrap();
        let expected = from_config(&config);
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(repo.path().join(".git/config"))
            .unwrap();
        file.write_all(text.as_bytes()).unwrap();
        drop(file);
        let node = crate::node::NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        assert_eq!(
            node.join_summary().unwrap().remote_snapshot().bindings,
            expected.bindings
        );
        assert!(expected.urls.iter().all(|url| !url.contains("secret")));
    }
}
