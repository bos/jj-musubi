//! One hive served alone on a transport, for tests of what travels between a node and its
//! hub: a hub serves its hives through `musubi_sync::server::HubServer`.

use std::sync::Arc;

use bytes::Bytes;
use musubi_sync::service::HubService;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HubReply;
use musubi_sync::wire::fit_error;
use musubi_transport::Transport;

/// Serves `service`'s requests on `rpc`, announcing new heads on `head`, until the
/// transport's subscription ends, calling `ready` once subscribed, when requests start being
/// answered. Requests are handled strictly one at a time, which is what makes every `Push`
/// atomic.
pub async fn serve_hive(
    mut service: HubService,
    transport: Arc<dyn Transport>,
    (rpc, head): (&str, &str),
    ready: impl FnOnce(),
) -> anyhow::Result<()> {
    let mut requests = transport.subscribe(rpc).await?;
    ready();
    while let Some(message) = requests.next().await {
        let Some(reply_to) = message.reply else {
            continue;
        };
        let (reply, notice) = match service.handle_bytes(&message.payload, transport.max_payload())
        {
            Ok(result) => result,
            Err(err) => {
                let error = fit_error(format!("{err:#}"), transport.max_payload());
                (Envelope::encode(HubReply::Error(error))?, None)
            }
        };
        transport.publish(&reply_to, Bytes::from(reply)).await.ok();
        if let Some(notice) = notice {
            let notice = Bytes::from(Envelope::encode(notice)?);
            transport.publish(head, notice).await.ok();
        }
    }
    Ok(())
}
