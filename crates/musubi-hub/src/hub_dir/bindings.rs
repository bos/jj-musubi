//! Whether a hive's remote names stay bound to one fetch and push destination each, across
//! what the hive recorded, what its copies' heads show, and what a joining or cloning copy
//! brings.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use musubi_jj::remote_url::RemoteBinding;

use super::Refusal;

/// The bindings of hive `hive`: those it `recorded`, with those its heads `observed` and then
/// those `incoming` added. Refused if its heads bind a name otherwise than the hive does, or
/// the incoming bindings bind one otherwise than both.
pub(super) fn checked(
    hive: &str,
    recorded: &BTreeMap<String, RemoteBinding>,
    observed: &BTreeMap<String, BTreeSet<RemoteBinding>>,
    incoming: &BTreeMap<String, RemoteBinding>,
) -> Result<BTreeMap<String, RemoteBinding>, Refusal> {
    let mut bindings = recorded.clone();
    let mut inconsistent = BTreeSet::new();
    for (name, observed) in observed {
        for binding in observed {
            if bindings.get(name).is_some_and(|old| old != binding) {
                inconsistent.insert(name.as_str());
            } else {
                bindings.insert(name.clone(), binding.clone());
            }
        }
    }
    if !inconsistent.is_empty() {
        return Err(format!(
            "hive {} has inconsistent recorded remotes: {}; make a new hive from a consistently configured copy",
            hive,
            inconsistent.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
    let mut conflicts = Vec::new();
    for (name, binding) in incoming {
        if bindings.get(name).is_some_and(|old| old != binding) {
            conflicts.push(name.as_str());
        } else {
            bindings.insert(name.clone(), binding.clone());
        }
    }
    if !conflicts.is_empty() {
        return Err(format!(
            "remote names {} have different fetch or push destinations than hive {} recorded; give different destinations different remote names before joining",
            conflicts.join(", "),
            hive
        ));
    }
    Ok(bindings)
}
