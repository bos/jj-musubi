//! Commands for inspecting the correspondence between local and hive operations.

use std::io::Write as _;
use std::path::Path;

use anyhow::Context as _;
use jj_lib::object_id::ObjectId as _;
use musubi_jj::op_id::LocalOp;

use crate::repo::Located;
use crate::ui::Ui;

pub fn op_id(ui: &Ui, start: &Path, id: &str) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let mut node = located.open()?;
    let prefix =
        jj_lib::object_id::HexPrefix::try_from_hex(id).context("not a hex operation id")?;
    let local = pollster::block_on(
        node.loader()
            .op_store()
            .resolve_operation_id_prefix(&prefix),
    )?;
    if let jj_lib::object_id::PrefixResolution::SingleMatch(local) = local {
        let local = LocalOp(local);
        let canonical = node.canonicalize(&local)?;
        writeln!(
            ui.stdout(),
            "local {} = hive {}",
            local.0.hex(),
            canonical.0.hex()
        )?;
        return Ok(());
    }
    if let Some(canonical) = node.canonical_store().resolve_prefix(id)? {
        match node.local_of(&canonical) {
            Some(local) => writeln!(
                ui.stdout(),
                "hive {} = local {}",
                canonical.0.hex(),
                local.0.hex()
            )?,
            None => writeln!(
                ui.stdout(),
                "hive {} is not realized on this machine yet",
                canonical.0.hex()
            )?,
        }
        return Ok(());
    }
    anyhow::bail!("no operation {id} here or in the hive")
}
