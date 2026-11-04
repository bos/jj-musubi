//! Recovery decisions outside the protocol model: the daemon pauses only a copy whose
//! history cannot be repaired by another sync. Error context must not change that decision.

use super::history_lost;
use musubi_jj::node::NodeError;
use musubi_transport::TransportError;

#[test]
fn permanent_history_loss_survives_error_context() {
    for cause in [
        NodeError::UnreachableHistory,
        NodeError::RewrittenRealization,
        NodeError::DamagedLog,
        NodeError::PrunedRecords,
    ] {
        let error = anyhow::Error::new(cause);
        assert!(history_lost(&error), "{error:#}");
        let error = error
            .context("applying the hub's reply")
            .context("sync failed");
        assert!(history_lost(&error), "{error:#}");
    }
}

#[test]
fn retryable_errors_do_not_pause_a_copy() {
    for error in [
        anyhow::Error::new(TransportError::Timeout),
        anyhow::Error::new(TransportError::Disconnected),
        anyhow::Error::new(NodeError::BeforeJoin("older operation".into())),
        anyhow::Error::new(NodeError::AmbiguousAbandon("retained operation".into())),
        anyhow::Error::new(NodeError::Io {
            path: "operation".into(),
            source: std::io::Error::from(std::io::ErrorKind::PermissionDenied),
        }),
        // The classification follows the typed cause, not a peer's or an I/O error's text.
        anyhow::anyhow!(NodeError::DamagedLog.to_string()),
    ] {
        let error = error.context("sync failed");
        assert!(!history_lost(&error), "{error:#}");
    }
}
