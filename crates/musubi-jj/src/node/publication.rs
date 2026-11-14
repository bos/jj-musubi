//! Content carried only for working-copy recovery history, and exact publication approvals.
//!
//! An explicit transaction protects its actual change outputs. Newly created working-copy
//! continuations (notably the unselected remainder of `jj commit PATH`) are not such outputs.
//! Native fixtures pin that jj boundary; `Musubi.Publication` specifies the set accounting.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::fs;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::backend::FileId;
use jj_lib::backend::SymlinkId;
use jj_lib::backend::TreeId;
use jj_lib::backend::TreeValue;
use jj_lib::config::ConfigGetResultExt as _;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::repo_path::RepoPathBuf;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;

use super::NodeError;
use super::NodeRepo;
use crate::op_id::CanonicalOp;

mod cleanup;
pub use cleanup::PublicationCleanup;
#[cfg(test)]
mod tests;

struct Checkpoint {
    id: CanonicalOp,
    operation: Operation,
    required: BTreeSet<CommitId>,
    intentional: BTreeSet<CommitId>,
}

pub const APPROVAL_FILE: &str = "publication-approval";
const OFFERS_FILE: &str = "publication-offers.json";

#[derive(Deserialize, Serialize)]
struct PublicationOffers {
    heads: Vec<String>,
    checksum: String,
}
pub const CHECKPOINT_ATTRIBUTE: &str = "musubi.publication-checkpoint";
pub(crate) const INTENT_ATTRIBUTE: &str = "musubi.publication-intent";

/// Cleanup freezes a survivor's source intent before changing its operation parents.
/// The declarations are also predecessor-record roots, not just exemptions from accounting.
pub(crate) fn retained_publication_intent(
    op: &Operation,
) -> Result<Option<BTreeSet<CommitId>>, String> {
    let Some(text) = op.metadata.attributes.get(INTENT_ATTRIBUTE) else {
        return Ok(None);
    };
    let ids: Vec<String> =
        serde_json::from_str(text).map_err(|err| format!("invalid retained intent: {err}"))?;
    let mut roots = BTreeSet::new();
    for id in ids {
        let id = CommitId::try_from_hex(&id).ok_or("invalid retained intent commit id")?;
        if !op
            .commit_predecessors
            .as_ref()
            .is_some_and(|writes| writes.contains_key(&id))
        {
            return Err("retained intent is not referenced by its operation".to_owned());
        }
        roots.insert(id);
    }
    Ok(Some(roots))
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct PublicationLimits {
    pub files: u64,
    pub bytes: u64,
}

impl PublicationLimits {
    pub fn load(settings: &jj_lib::settings::UserSettings) -> Result<Self, NodeError> {
        let config = settings.config();
        Ok(Self {
            files: config
                .get("musubi.publication.max-files")
                .optional()?
                .unwrap_or(100),
            bytes: config
                .get_value_with(
                    "musubi.publication.max-bytes",
                    jj_lib::settings::HumanByteSize::try_from,
                )
                .optional()?
                .map_or(8 * 1024 * 1024, |bytes| bytes.0),
        })
    }

    pub fn fits(self, files: u64, bytes: u64) -> bool {
        (self.files == 0 || files <= self.files) && (self.bytes == 0 || bytes <= self.bytes)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationFile {
    pub path: String,
    pub bytes: u64,
    pub versions: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationOperation {
    /// An unambiguous local jj operation prefix, usable with jj and the cleanup selector.
    pub id: String,
    pub description: String,
    pub snapshot: bool,
    pub files: usize,
    pub bytes: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationReport {
    pub token: String,
    pub files: Vec<PublicationFile>,
    pub bytes: u64,
    pub operations: Vec<PublicationOperation>,
    pub limits: PublicationLimits,
    pub cleanup_available: bool,
    #[serde(skip)]
    content: BTreeSet<FileVersion>,
}

impl PublicationReport {
    pub fn held(&self) -> bool {
        !self.limits.fits(self.files.len() as u64, self.bytes)
    }
}

#[derive(Debug, Error)]
#[error(
    "sending held: snapshots retain {files} files ({bytes} bytes), exceeding the publication budget\nHint: run `musubi sync --outgoing` to inspect or approve them"
)]
pub struct PublicationHeld {
    pub files: usize,
    pub bytes: u64,
}

#[derive(Default)]
pub struct PublicationCache {
    base: Option<CanonicalOp>,
    known: Closure,
    sizes: BTreeMap<ContentId, u64>,
    last: Option<(
        Vec<CanonicalOp>,
        CanonicalOp,
        PublicationLimits,
        PublicationReport,
    )>,
}

#[derive(Default)]
struct Closure {
    commits: HashSet<CommitId>,
    trees: HashSet<(RepoPathBuf, TreeId)>,
    files: HashSet<ContentId>,
    versions: BTreeSet<FileVersion>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FileVersion {
    path: RepoPathBuf,
    id: ContentId,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ContentId {
    File(FileId),
    Symlink(SymlinkId),
    Submodule(CommitId),
}

/// Explicit reference targets retain their history role even when also working-copy tips.
fn reference_roots(view: &View) -> BTreeSet<CommitId> {
    let mut roots = BTreeSet::new();
    for target in view
        .local_bookmarks
        .values()
        .chain(view.local_tags.values())
        .chain(view.git_refs.values())
        .chain(view.git_heads.values())
    {
        roots.extend(target.iter().flatten().cloned());
    }
    for remote in view.remote_views.values() {
        for reference in remote.bookmarks.values().chain(remote.tags.values()) {
            roots.extend(reference.target.iter().flatten().cloned());
        }
    }
    roots
}

/// The exact root references in a view, without operation predecessor records.
fn view_roots(view: &View) -> BTreeSet<CommitId> {
    let mut roots = reference_roots(view);
    roots.extend(view.head_ids.iter().cloned());
    roots.extend(view.wc_commit_ids.values().cloned());
    roots
}

/// Parse jj's rendered comma-separated symbol list against the view's actual names.
/// Longest matches keep commas and quotes inside a rendered name from becoming separators.
fn named_selections(
    mut names: &str,
    candidates: Vec<(String, BTreeSet<CommitId>)>,
) -> Option<BTreeSet<CommitId>> {
    let mut selected = BTreeSet::new();
    while !names.is_empty() {
        let (name, roots) = candidates
            .iter()
            .filter(|(name, _)| {
                names == name
                    || names
                        .strip_prefix(name.as_str())
                        .is_some_and(|rest| rest.starts_with(", "))
            })
            .max_by_key(|(name, _)| name.len())?;
        selected.extend(roots.iter().cloned());
        names = &names[name.len()..];
        if let Some(rest) = names.strip_prefix(", ") {
            names = rest;
        }
    }
    Some(selected)
}

/// Decode the pinned jj CLI's argument rendering (not POSIX shell quoting).
fn recorded_arg(input: &mut &str) -> Option<String> {
    let mut chars = input.char_indices().peekable();
    let quoted = chars.peek()?.1 == '\'';
    if quoted {
        chars.next();
    }
    let mut value = String::new();
    while let Some((offset, ch)) = chars.next() {
        if quoted && ch == '\\' && chars.peek().is_some_and(|(_, next)| *next == '\'') {
            // jj renders a literal apostrophe and a trailing backslash before the
            // closing delimiter ambiguously. Never guess across that token boundary.
            return None;
        } else if (quoted && ch == '\'') || (!quoted && ch == ' ') {
            let rest = &input[offset + ch.len_utf8()..];
            *input = if quoted && !rest.is_empty() {
                rest.strip_prefix(' ')?
            } else {
                rest
            };
            return Some(value);
        } else {
            if !quoted && !(ch.is_ascii_alphanumeric() || ",-./:@_".contains(ch)) {
                return None;
            }
            value.push(ch);
        }
    }
    if quoted {
        None
    } else {
        *input = "";
        Some(value)
    }
}

/// Whether jj's recorded arguments explicitly invoke Git import, init or clone.
pub fn explicit_git_import(mut args: &str) -> bool {
    if recorded_arg(&mut args).as_deref() != Some("jj") {
        return false;
    }
    let mut git = false;
    while let Some(arg) = recorded_arg(&mut args) {
        let (name, attached) = arg
            .split_once('=')
            .map_or((arg.as_str(), None), |(k, v)| (k, Some(v)));
        if [
            "--repository",
            "-R",
            "--at-operation",
            "--at-op",
            "--color",
            "--config",
            "--config-file",
        ]
        .contains(&name)
        {
            if attached.is_none() && recorded_arg(&mut args).is_none() {
                return false;
            }
        } else if ([
            "--ignore-working-copy",
            "--no-integrate-operation",
            "--ignore-immutable",
            "--debug",
            "--quiet",
            "--no-pager",
        ]
        .contains(&name)
            && attached.is_none())
            || (arg.starts_with("-R") && arg.len() > 2)
        {
            continue;
        } else if !git && arg == "git" {
            git = true;
        } else {
            return git && ["import", "init", "clone"].contains(&arg.as_str());
        }
    }
    false
}

fn recorded_explicit_import(op: &Operation) -> bool {
    op.metadata
        .attributes
        .get("args")
        .is_some_and(|args| explicit_git_import(args))
}

fn automatic_git_bookkeeping(op: &Operation) -> bool {
    op.metadata.description == "export git refs"
        || (["import git refs", "import git head"].contains(&op.metadata.description.as_str())
            && !recorded_explicit_import(op))
}

impl NodeRepo {
    pub(in crate::node) fn publication_namespace_facts(
        &self,
        head: &CanonicalOp,
    ) -> Result<BTreeMap<String, String>, NodeError> {
        let view = self.canonical.read_operation_view(head)?;
        let presence = self.presence(head)?;
        let namespace = self.workspace_context_of_view(&view, &presence)?;
        let own = crate::canonical::namespace::Namespace {
            source: self.machine.key().to_owned(),
            known: BTreeSet::from([self.machine.key().to_owned()]),
            names: view
                .wc_commit_ids
                .keys()
                .filter_map(|key| {
                    let (owner, name) = crate::workspaces::split_key(key.as_str())?;
                    (owner == self.machine.key())
                        .then(|| (name.to_owned(), key.as_str().to_owned()))
                })
                .collect(),
        };
        Ok(BTreeMap::from([
            (crate::canonical::namespace::ATTRIBUTE.to_owned(), namespace),
            (super::view::LOCAL_WORKSPACES.to_owned(), own.encode()),
        ]))
    }

    fn publication_foreign_presence(&self, head: &CanonicalOp) -> Result<String, NodeError> {
        let stamp = self.presence(head)?.to_stamp(|work| work.original.hex());
        Ok(stamp
            .lines()
            .filter(|line| line.split_whitespace().nth(1) != Some(self.machine.key()))
            .collect::<Vec<_>>()
            .join("\n"))
    }

    /// Start tracking before the first attempt under this guard. Existing copies freeze
    /// their pre-activation heads: latest-push markers cannot rule out an older lost reply.
    pub fn initialize_publication_offers(&mut self) -> Result<(), NodeError> {
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        if path.exists() {
            return Ok(());
        }
        let legacy = ["pushed", "accepted_push", "accepted_base"]
            .iter()
            .any(|name| self.repo_path.join("musubi").join(name).exists());
        let mut heads = if legacy {
            self.canonical_heads()?
        } else {
            vec![]
        };
        for name in ["pushed", "accepted_push"] {
            match fs::read_to_string(self.repo_path.join("musubi").join(name)) {
                Ok(text) => {
                    let id = OperationId::try_from_hex(text.trim())
                        .filter(|id| {
                            id.as_bytes().len()
                                == self.canonical.root_operation_id().0.as_bytes().len()
                        })
                        .ok_or_else(|| {
                            NodeError::Publication(format!(
                                "cannot establish publication history from {name}"
                            ))
                        })?;
                    heads.push(CanonicalOp(id));
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(source) => {
                    return Err(NodeError::Io {
                        path: path.clone(),
                        source,
                    });
                }
            }
        }
        use std::io::Write as _;
        let data = Self::encode_publication_offers(&heads)?;
        match fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
        {
            Ok(mut file) => file
                .write_all(&data)
                .map_err(|source| NodeError::Io { path, source }),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => Ok(()),
            Err(source) => Err(NodeError::Io { path, source }),
        }
    }

    fn read_publication_offers(&self) -> Result<Vec<CanonicalOp>, NodeError> {
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        let text = fs::read_to_string(&path).map_err(|source| NodeError::Io {
            path: path.clone(),
            source,
        })?;
        let encoded: PublicationOffers = serde_json::from_str(&text).map_err(|err| {
            NodeError::Publication(format!(
                "cannot read this copy's record of attempted publications: {err}"
            ))
        })?;
        let body = serde_json::to_vec(&encoded.heads)
            .map_err(|err| NodeError::Publication(err.to_string()))?;
        if blake3::hash(&body).to_hex().as_str() != encoded.checksum {
            return Err(NodeError::Publication(
                "cannot read this copy's record of attempted publications: checksum mismatch"
                    .to_owned(),
            ));
        }
        encoded
            .heads
            .into_iter()
            .map(|hex| {
                let id = OperationId::try_from_hex(&hex)
                    .filter(|id| {
                        id.as_bytes().len() == self.canonical.root_operation_id().0.as_bytes().len()
                    })
                    .map(CanonicalOp)
                    .ok_or_else(|| {
                        NodeError::Publication("invalid attempted publication identity".to_owned())
                    })?;
                if !self.canonical.has_operation(&id) {
                    return Err(NodeError::Publication(
                        "the source history of an attempted publication is missing".to_owned(),
                    ));
                }
                Ok(id)
            })
            .collect()
    }

    fn encode_publication_offers(heads: &[CanonicalOp]) -> Result<Vec<u8>, NodeError> {
        let values: BTreeSet<_> = heads.iter().map(|id| id.0.hex()).collect();
        let heads: Vec<_> = values.into_iter().collect();
        let body =
            serde_json::to_vec(&heads).map_err(|err| NodeError::Publication(err.to_string()))?;
        let offers = PublicationOffers {
            heads,
            checksum: blake3::hash(&body).to_hex().to_string(),
        };
        serde_json::to_vec(&offers).map_err(|err| NodeError::Publication(err.to_string()))
    }

    fn write_publication_offers(&self, heads: &[CanonicalOp]) -> Result<(), NodeError> {
        use std::io::Write as _;
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        let data = Self::encode_publication_offers(heads)?;
        if fs::read(&path).ok().as_deref() == Some(&data) {
            return Ok(());
        }
        let write = || -> std::io::Result<()> {
            let mut file = fs::OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(false)
                .open(&path)?;
            file.write_all(&data)?;
            file.set_len(data.len() as u64)
        };
        write().map_err(|source| NodeError::Io { path, source })
    }

    /// A compact frontier of every attempted upload. Only exact ancestry can subsume an
    /// older offer: a contraction may preserve its head's original identity while dropping
    /// ancestors that were part of the original upload.
    pub fn record_publication_offer(&mut self, head: &CanonicalOp) -> Result<(), NodeError> {
        self.initialize_publication_offers()?;
        let previous = self.read_publication_offers()?;
        for old in &previous {
            if self.canonical.is_ancestor_of(head, old)? {
                return Ok(());
            }
        }
        let mut next = vec![];
        for old in previous {
            if !self.canonical.is_ancestor_of(&old, head)? {
                next.push(old);
            }
        }
        next.push(head.clone());
        self.write_publication_offers(&next)
    }

    fn publication_offered_origins(&self) -> Result<HashSet<OperationId>, NodeError> {
        let offered = self.read_publication_offers()?;
        let mut pending = offered;
        let mut seen = HashSet::new();
        let mut origins = HashSet::new();
        while let Some(id) = pending.pop() {
            if id == *self.canonical.root_operation_id() || !seen.insert(id.clone()) {
                continue;
            }
            // ancestors_until deliberately skips missing bodies for other callers. A gap
            // cannot establish that an operation was never offered, so read strictly here.
            let operation = self.canonical.read_operation(&id)?;
            origins.insert(self.canonical.original_id(&id)?);
            pending.extend(operation.parents.into_iter().map(CanonicalOp));
        }
        Ok(origins)
    }

    fn publication_facts(
        &self,
        id: &CanonicalOp,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        if let Some(roots) = retained_publication_intent(op).map_err(NodeError::Publication)? {
            return Ok((roots, true));
        }
        if op.metadata.attributes.contains_key(CHECKPOINT_ATTRIBUTE) {
            return Ok((
                op.commit_predecessors
                    .iter()
                    .flatten()
                    .map(|(id, _)| id.clone())
                    .collect(),
                true,
            ));
        }
        if self.joins.values().any(|join| join == id) {
            return self.publication_initial_facts(id);
        }
        self.publication_command_intent(op, view)
    }

    fn publication_intent_is_uncertain(
        &self,
        id: &CanonicalOp,
        op: &Operation,
    ) -> Result<bool, NodeError> {
        Ok(!self
            .publication_facts(id, op, &self.canonical.read_view(&op.view_id)?)?
            .1)
    }

    fn publication_intentional(
        &self,
        id: &CanonicalOp,
        op: &Operation,
        view: &View,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Ok(self.publication_facts(id, op, view)?.0)
    }

    /// Pre-join native history supplies intrinsic command facts, never a reconstruction
    /// of before/after roles. Missing or unrecognized facts also block destructive cleanup.
    fn publication_initial_facts(
        &self,
        join: &CanonicalOp,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        let source = self.local_of(join).ok_or_else(|| {
            NodeError::Publication("the initial join's source history is missing".to_owned())
        })?;
        let store = self.loader.op_store();
        let mut stack = vec![source.0];
        let mut seen = HashSet::new();
        let mut roots = BTreeSet::new();
        let mut known = true;
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            let op = store.read_operation(&id).block_on()?;
            stack.extend(op.parents.iter().cloned());
            if let Some(intent) =
                retained_publication_intent(&op).map_err(NodeError::Publication)?
            {
                roots.extend(intent);
                continue;
            }
            if op.metadata.attributes.contains_key(CHECKPOINT_ATTRIBUTE) {
                roots.extend(
                    op.commit_predecessors
                        .iter()
                        .flatten()
                        .map(|(id, _)| id.clone()),
                );
                continue;
            }
            let view = store.read_view(&op.view_id).block_on()?;
            if let Some(intent) = self.publication_git_intent(&op, &view)? {
                roots.extend(intent);
                continue;
            }
            let (selected, complete) = self.publication_command_intent(&op, &view)?;
            roots.extend(selected);
            known &= complete;
        }
        let view = self.canonical.read_operation_view(join)?;
        let required = self.publication_commit_closure(view_roots(&view))?;
        roots.retain(|id| required.contains(id));
        Ok((roots, known))
    }

    #[cfg(test)]
    fn publication_initial_intentional(
        &self,
        join: &CanonicalOp,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Ok(self.publication_initial_facts(join)?.0)
    }

    fn publication_automatic(op: &Operation) -> bool {
        op.metadata.is_snapshot
            || op.metadata.description == "reconcile divergent operations"
            || op.metadata.description.starts_with("musubi:")
    }

    /// Intention must survive arbitrary operation reparenting and native GC. Creation
    /// records and explicit selected revisions do; differences against parent views do not.
    fn publication_command_intent(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        if Self::publication_automatic(op) {
            return Ok((BTreeSet::new(), true));
        }
        if automatic_git_bookkeeping(op) {
            return Ok((BTreeSet::new(), false));
        }
        let mut roots = self.publication_recorded_outputs(op, view)?;
        let (selected, known) = self.publication_selections(op, view)?;
        roots.extend(selected);
        Ok((roots, known))
    }

    /// Before stripping private Git refs, establish that every possible selected target is
    /// already covered by actual written outputs. Existing unexplained targets are uncertain;
    /// importing an unrelated ref must not approve an automatically moved bookmark.
    pub(super) fn publication_git_intent(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<Option<BTreeSet<CommitId>>, NodeError> {
        if !["import git refs", "import git head"].contains(&op.metadata.description.as_str())
            || op.metadata.attributes.contains_key(INTENT_ATTRIBUTE)
            || Self::publication_automatic(op)
            || !recorded_explicit_import(op)
        {
            return Ok(None);
        }
        let roots = self.publication_recorded_outputs(op, view)?;
        let covered = self.publication_commit_closure(roots.iter().cloned())?;
        let complete = view
            .git_refs
            .values()
            .chain(view.git_heads.values())
            .flat_map(|target| target.iter().flatten())
            .all(|id| covered.contains(id));
        Ok(complete.then_some(roots))
    }

    /// The pinned jj CLI records full selected commit ids in these command descriptions.
    /// Native fixtures pin those forms; unknown records remain conservative.
    fn publication_selections(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        let description = op.metadata.description.as_str();
        let selected = if let Some(id) = description.strip_prefix("edit commit ") {
            Some((id, true))
        } else if description.starts_with("create bookmark ") {
            description
                .rsplit_once(" pointing to commit ")
                .map(|(_, id)| (id, false))
        } else if description.starts_with("point bookmark ") || description.starts_with("set tag ")
        {
            description
                .rsplit_once(" to commit ")
                .map(|(_, id)| (id, false))
        } else {
            None
        };
        if let Some((text, edit)) = selected {
            // `jj diffedit` uses the same description as `jj edit`, but names the old
            // target. Its rewritten output is intentional; the old input gains no exemption.
            if edit
                && CommitId::try_from_hex(text).is_some_and(|id| {
                    op.commit_predecessors
                        .iter()
                        .flatten()
                        .any(|(_, previous)| previous.contains(&id))
                })
            {
                return Ok((BTreeSet::new(), true));
            }
            let id = CommitId::try_from_hex(text).filter(|id| {
                if edit {
                    view.wc_commit_ids.values().any(|tip| tip == id)
                } else {
                    reference_roots(view).contains(id)
                }
            });
            return Ok(match id {
                Some(id) => (BTreeSet::from([id]), true),
                None => (BTreeSet::new(), false),
            });
        }
        if let Some(names) = description.strip_prefix("fetch from git remote(s) ") {
            let candidates = view
                .remote_views
                .iter()
                .map(|(name, remote)| {
                    let roots = remote
                        .bookmarks
                        .values()
                        .chain(remote.tags.values())
                        .flat_map(|reference| reference.target.iter().flatten().cloned())
                        .collect();
                    (name.as_symbol().to_string(), roots)
                })
                .collect();
            return Ok(named_selections(names, candidates)
                .map_or_else(|| (BTreeSet::new(), false), |roots| (roots, true)));
        }
        if description == "fetch from git remote into empty repo" {
            let roots = view
                .remote_views
                .values()
                .flat_map(|remote| remote.bookmarks.values().chain(remote.tags.values()))
                .flat_map(|reference| reference.target.iter().flatten().cloned())
                .collect();
            return Ok((roots, true));
        }
        if ["import git head", "import git refs"].contains(&description) {
            // A complete native import freezes its output roots before private refs
            // disappear. Without that evidence, existing selected targets are uncertain.
            return Ok((BTreeSet::new(), false));
        }
        if description == "export git refs" {
            // jj also retries failed automatic exports under this description. It is
            // not evidence that the user selected its unchanged bookmark targets.
            return Ok((BTreeSet::new(), false));
        }
        for (prefix, tags) in [
            ("track remote bookmark ", false),
            ("track remote tag ", true),
        ] {
            if let Some(names) = description.strip_prefix(prefix) {
                let candidates = view
                    .remote_views
                    .iter()
                    .flat_map(|(remote, refs)| {
                        let refs = if tags { &refs.tags } else { &refs.bookmarks };
                        refs.iter().map(move |(name, reference)| {
                            (
                                name.to_remote_symbol(remote).to_string(),
                                reference.target.iter().flatten().cloned().collect(),
                            )
                        })
                    })
                    .collect();
                return Ok(named_selections(names, candidates)
                    .map_or_else(|| (BTreeSet::new(), false), |roots| (roots, true)));
            }
        }
        let writes_known = op.commit_predecessors.is_some()
            && [
                "commit ",
                "describe ",
                "new empty commit",
                "split ",
                "squash ",
                "rebase ",
                "restore into commit ",
                "revert ",
                "backout ",
                "duplicate ",
                "parallelize ",
                "simplify ",
                "resolve ",
                "Resolve conflicts in commit ",
                "diffedit ",
                "diff edit ",
                "fix ",
                "fixed ",
                "apply fixes",
                "absorb changes into ",
                "arrange revisions",
                "converge ",
                "run: rewrite ",
                "run: nothing changed",
                "track paths",
                "untrack paths",
                "delete paths in commit ",
                "make paths ",
                "edit file ",
                "sign ",
                "unsign ",
                "abandon ",
                "initialize ",
                "create initial working-copy commit",
                "add workspace ",
                "check out git remote's branch: ",
            ]
            .iter()
            .any(|prefix| description.starts_with(prefix));
        let names_only = [
            "delete bookmark ",
            "forget bookmark ",
            "rename bookmark ",
            "untrack remote bookmark ",
            "delete tag ",
            "untrack remote tag ",
            "forget workspace ",
            "forget workspaces ",
            "rename workspace ",
            "Renamed workspace ",
            "add git remote ",
            "remove git remote ",
            "rename git remote ",
            "set git remote ",
        ]
        .iter()
        .any(|prefix| description.starts_with(prefix));
        let root = op.parents.is_empty() && description.is_empty();
        Ok((BTreeSet::new(), writes_known || names_only || root))
    }

    fn publication_commit_closure(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        let mut pending: Vec<_> = roots.into_iter().collect();
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if seen.insert(id.clone()) {
                pending.extend(
                    self.loader
                        .store()
                        .get_commit(&id)?
                        .parent_ids()
                        .iter()
                        .cloned(),
                );
            }
        }
        Ok(seen)
    }

    fn publication_recorded_outputs(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        let tips: HashSet<_> = view.wc_commit_ids.values().collect();
        let mut roots: BTreeSet<_> = op
            .commit_predecessors
            .iter()
            .flatten()
            .filter(|(id, previous)| !tips.contains(id) || !previous.is_empty())
            .map(|(id, _)| id.clone())
            .collect();
        // `jj new REV` deliberately chooses REV even when it was already a visible
        // descendant. A partial commit's continuation merely points to its intended output.
        for (id, previous) in op.commit_predecessors.iter().flatten() {
            if previous.is_empty() && tips.contains(id) {
                roots.extend(
                    self.loader
                        .store()
                        .get_commit(id)?
                        .parent_ids()
                        .iter()
                        .cloned(),
                );
            }
        }
        Ok(roots)
    }

    /// All raw tree sides are walked, including a directory side of a file/directory
    /// conflict. MergedTree::entries deliberately does not descend those directories.
    fn publication_closure(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        into: &mut Closure,
        skip: &Closure,
    ) -> Result<(), NodeError> {
        let store = self.loader.store();
        let mut commits: Vec<_> = roots.into_iter().collect();
        while let Some(id) = commits.pop() {
            if skip.commits.contains(&id) || !into.commits.insert(id.clone()) {
                continue;
            }
            let commit = store.get_commit(&id)?;
            commits.extend(commit.parent_ids().iter().cloned());
            let mut trees: Vec<_> = commit
                .tree_ids()
                .iter()
                .map(|id| (RepoPathBuf::root(), id.clone()))
                .collect();
            while let Some((path, id)) = trees.pop() {
                if skip.trees.contains(&(path.clone(), id.clone()))
                    || !into.trees.insert((path.clone(), id.clone()))
                {
                    continue;
                }
                let tree = store.get_tree(path.clone(), &id).block_on()?;
                for entry in tree.entries_non_recursive() {
                    match entry.value() {
                        TreeValue::File { id, .. } => {
                            let id = ContentId::File(id.clone());
                            into.files.insert(id.clone());
                            into.versions.insert(FileVersion {
                                path: path.join(entry.name()),
                                id,
                            });
                        }
                        TreeValue::Tree(id) => trees.push((path.join(entry.name()), id.clone())),
                        TreeValue::Symlink(id) => {
                            let id = ContentId::Symlink(id.clone());
                            into.files.insert(id.clone());
                            into.versions.insert(FileVersion {
                                path: path.join(entry.name()),
                                id,
                            });
                        }
                        TreeValue::GitSubmodule(id) => {
                            let id = ContentId::Submodule(id.clone());
                            into.files.insert(id.clone());
                            into.versions.insert(FileVersion {
                                path: path.join(entry.name()),
                                id,
                            });
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn publication_files(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        known: &Closure,
        intentional: &Closure,
    ) -> Result<BTreeSet<FileVersion>, NodeError> {
        let store = self.loader.store();
        let mut files = BTreeSet::new();
        let mut commits: Vec<_> = roots.into_iter().collect();
        let mut seen_commits = HashSet::new();
        let mut seen_trees = HashSet::new();
        while let Some(id) = commits.pop() {
            if known.commits.contains(&id)
                || intentional.commits.contains(&id)
                || !seen_commits.insert(id.clone())
            {
                continue;
            }
            let commit = store.get_commit(&id)?;
            commits.extend(commit.parent_ids().iter().cloned());
            let mut trees: Vec<_> = commit
                .tree_ids()
                .iter()
                .map(|id| (RepoPathBuf::root(), id.clone()))
                .collect();
            while let Some((path, id)) = trees.pop() {
                if known.trees.contains(&(path.clone(), id.clone()))
                    || intentional.trees.contains(&(path.clone(), id.clone()))
                    || !seen_trees.insert((path.clone(), id.clone()))
                {
                    continue;
                }
                let tree = store.get_tree(path.clone(), &id).block_on()?;
                for entry in tree.entries_non_recursive() {
                    let path = path.join(entry.name());
                    match entry.value() {
                        TreeValue::File { id, .. } => {
                            let file = FileVersion {
                                path,
                                id: ContentId::File(id.clone()),
                            };
                            if !known.versions.contains(&file)
                                && !intentional.versions.contains(&file)
                            {
                                files.insert(file);
                            }
                        }
                        TreeValue::Symlink(id) => {
                            let file = FileVersion {
                                path,
                                id: ContentId::Symlink(id.clone()),
                            };
                            if !known.versions.contains(&file)
                                && !intentional.versions.contains(&file)
                            {
                                files.insert(file);
                            }
                        }
                        TreeValue::GitSubmodule(id) => {
                            let file = FileVersion {
                                path,
                                id: ContentId::Submodule(id.clone()),
                            };
                            if !known.versions.contains(&file)
                                && !intentional.versions.contains(&file)
                            {
                                files.insert(file);
                            }
                        }
                        TreeValue::Tree(id) => trees.push((path, id.clone())),
                    }
                }
            }
        }
        Ok(files)
    }

    fn publication_content_bytes(&self, file: &FileVersion) -> Result<u64, NodeError> {
        match &file.id {
            ContentId::File(id) => {
                let mut reader = self.loader.store().read_file(&file.path, id).block_on()?;
                futures::io::copy(&mut reader, &mut futures::io::sink())
                    .block_on()
                    .map_err(|source| NodeError::Io {
                        path: self.repo_path.clone(),
                        source,
                    })
            }
            ContentId::Symlink(id) => Ok(self
                .loader
                .store()
                .read_symlink(&file.path, id)
                .block_on()?
                .len() as u64),
            ContentId::Submodule(_) => Ok(0),
        }
    }

    /// The immutable publication's extra content. Known object closure is extended once as
    /// the accepted basis advances, and rebuilt when it goes back or changes branches.
    pub fn publication_report(
        &mut self,
        ops: &[CanonicalOp],
        base: &CanonicalOp,
        cache: &mut PublicationCache,
    ) -> Result<PublicationReport, NodeError> {
        self.publication_report_projected(ops, base, cache, None)
    }

    fn publication_report_projected(
        &self,
        ops: &[CanonicalOp],
        base: &CanonicalOp,
        cache: &mut PublicationCache,
        checkpoint: Option<Checkpoint>,
    ) -> Result<PublicationReport, NodeError> {
        let limits = PublicationLimits::load(self.loader.settings())?;
        let projected = checkpoint.is_some();
        if !projected
            && let Some((previous, basis, old_limits, report)) = &cache.last
            && previous == ops
            && basis == base
            && *old_limits == limits
        {
            return Ok(report.clone());
        }
        if cache.base.as_ref() != Some(base) {
            if cache
                .base
                .as_ref()
                .is_some_and(|old| !self.canonical.is_ancestor_of(old, base).unwrap_or(false))
            {
                cache.known = Closure::default();
                cache.base = None;
            }
            let stop = cache.base.as_ref();
            let previous = self
                .canonical
                .ancestors_until(std::slice::from_ref(base), |id| Some(id) == stop)?;
            let roots = self.required_commits(&previous)?;
            self.publication_closure(roots, &mut cache.known, &Closure::default())?;
            cache.base = Some(base.clone());
        }
        let mut details = vec![];
        let mut protected = BTreeSet::new();
        let mut cleanup_available = true;
        for id in ops {
            let op = self.canonical.read_operation(id)?;
            let view = self.canonical.read_view(&op.view_id)?;
            let (intentional, known) = self.publication_facts(id, &op, &view)?;
            protected.extend(intentional);
            cleanup_available &= known;
            let roots = self.required_commits(std::slice::from_ref(id))?;
            details.push((id.clone(), op, roots));
        }
        if let Some(checkpoint) = checkpoint {
            protected.extend(checkpoint.intentional);
            details.push((checkpoint.id, checkpoint.operation, checkpoint.required));
        }
        let mut intentional = Closure::default();
        self.publication_closure(protected, &mut intentional, &cache.known)?;
        let mut all = BTreeSet::new();
        let mut contributions = vec![];
        for (id, op, roots) in details {
            let files = self.publication_files(roots, &cache.known, &intentional)?;
            all.extend(files.iter().cloned());
            contributions.push((id, op, files));
        }
        let mut sizes = BTreeMap::new();
        for file in &all {
            if !sizes.contains_key(&file.id) {
                if cache.known.files.contains(&file.id) || intentional.files.contains(&file.id) {
                    sizes.insert(file.id.clone(), 0);
                    continue;
                }
                let bytes = match cache.sizes.get(&file.id) {
                    Some(bytes) => *bytes,
                    None => {
                        let bytes = self.publication_content_bytes(file)?;
                        cache.sizes.insert(file.id.clone(), bytes);
                        bytes
                    }
                };
                sizes.insert(file.id.clone(), bytes);
            }
        }
        let bytes_of = |files: &BTreeSet<FileVersion>| -> u64 {
            files
                .iter()
                .map(|f| &f.id)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .map(|id| sizes[id])
                .fold(0_u64, u64::saturating_add)
        };
        let bytes = bytes_of(&all);
        let mut paths: BTreeMap<String, (u64, usize)> = BTreeMap::new();
        for file in &all {
            let total = paths
                .entry(file.path.as_internal_file_string().to_owned())
                .or_default();
            total.0 = total.0.saturating_add(sizes[&file.id]);
            total.1 += 1;
        }
        let pending_ids: Vec<_> = ops
            .iter()
            .map(|id| {
                self.local_of(id)
                    .map_or_else(|| id.0.hex(), |local| local.0.hex())
            })
            .collect();
        let prefix = |id: String| {
            let length = (12..=id.len())
                .find(|length| {
                    pending_ids
                        .iter()
                        .filter(|other| other.starts_with(&id[..*length]))
                        .count()
                        == 1
                })
                .unwrap_or(id.len());
            id[..length].to_owned()
        };
        let operations = contributions
            .into_iter()
            .filter(|(_, _, files)| !files.is_empty())
            .map(|(id, op, files)| PublicationOperation {
                id: prefix(
                    self.local_of(&id)
                        .map_or_else(|| id.0.hex(), |local| local.0.hex()),
                ),
                description: op.metadata.description,
                snapshot: op.metadata.is_snapshot,
                files: files.iter().map(|f| &f.path).collect::<BTreeSet<_>>().len(),
                bytes: bytes_of(&files),
            })
            .collect();
        let mut hash = blake3::Hasher::new();
        hash.update(self.machine.key().as_bytes());
        hash.update(base.0.as_bytes());
        hash.update(&limits.files.to_le_bytes());
        hash.update(&limits.bytes.to_le_bytes());
        let mut ordered = ops.to_vec();
        ordered.sort();
        for id in &ordered {
            hash.update(id.0.as_bytes());
        }
        hash.update(&bytes.to_le_bytes());
        hash.update(&(all.len() as u64).to_le_bytes());
        for file in &all {
            let path = file.path.as_internal_file_string();
            hash.update(&(path.len() as u64).to_le_bytes());
            hash.update(path.as_bytes());
            let (kind, id) = match &file.id {
                ContentId::File(id) => (0_u8, id.as_bytes()),
                ContentId::Symlink(id) => (1_u8, id.as_bytes()),
                ContentId::Submodule(id) => (2_u8, id.as_bytes()),
            };
            hash.update(&[kind]);
            hash.update(&(id.len() as u64).to_le_bytes());
            hash.update(id);
        }
        let token = hash.finalize().to_hex().to_string();
        let report = PublicationReport {
            content: all,
            token,
            bytes,
            limits,
            cleanup_available,
            operations,
            files: paths
                .into_iter()
                .map(|(path, (bytes, versions))| PublicationFile {
                    path,
                    bytes,
                    versions,
                })
                .collect(),
        };
        if !projected {
            cache.last = Some((ops.to_vec(), base.clone(), limits, report.clone()));
        }
        Ok(report)
    }

    /// Reads the latest accepted basis, without contacting the hub or snapshotting files.
    pub fn outgoing_publication(
        &mut self,
        cache: &mut PublicationCache,
    ) -> Result<PublicationReport, NodeError> {
        self.settle()?;
        self.check_abandon()?;
        let base = self
            .stored_base()
            .map_or_else(|| self.canonical.root_operation_id().clone(), |op| op.0);
        let heads = self.canonical_heads()?;
        let excluded: HashSet<_> = self
            .canonical
            .ancestors_until(std::slice::from_ref(&base), |_| false)?
            .into_iter()
            .collect();
        let ops = self
            .canonical
            .ancestors_until(&heads, |id| excluded.contains(id))?;
        self.publication_report(&ops, &base, cache)
    }
}

/// Shared by CLI approval/cleanup and every sender, held before any attachment upload.
pub fn publication_lock(repo: &Path) -> std::io::Result<fs::File> {
    let path = repo.join("musubi/publication.lock");
    let file = fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(path)?;
    file.lock()?;
    Ok(file)
}

pub fn approve_publication(
    repo: &Path,
    report: &PublicationReport,
    token: &str,
) -> std::io::Result<bool> {
    if token != report.token {
        return Ok(false);
    }
    crate::files::replace(&repo.join("musubi").join(APPROVAL_FILE), token.as_bytes())?;
    Ok(true)
}

pub fn publication_approved(repo: &Path, report: &PublicationReport) -> bool {
    fs::read_to_string(repo.join("musubi").join(APPROVAL_FILE))
        .is_ok_and(|token| token == report.token)
}
