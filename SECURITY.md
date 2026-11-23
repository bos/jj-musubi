# Security

Report a vulnerability privately, through
[GitHub](https://github.com/bos/jj-musubi/security/advisories/new), not in a public issue.
Only the latest release gets fixes.

## What jj-musubi protects

Anyone authorized to connect to a hub can read and write every hive on it. A hub always serves
a local socket restricted to its own user. Other machines connect over ssh with a key allowed
only to run `musubi hub connect`, or over TLS with an authorized client certificate.

TLS invitations pin the hub's certificate and carry a random enrollment secret. Invitations
are 48 English words: two checksummed 24-word groups encoding
the full 256-bit hub pin and secret. The lookup id is domain-separated SHA256 of the secret;
it identifies an invitation but does not authorize enrollment without the secret. The checksums
detect some transcription errors; they do not make a disclosed invitation safe to share
publicly.
The client verifies the hub before disclosing the secret, generates its private key locally, and
proves possession during enrollment. The hub checks the invitation secret before parsing or
signing the certificate request, then checks it again while atomically consuming a single-use
invitation. Unauthenticated TLS connections can only attempt enrollment; they cannot access
hives or management operations. Invitations contain no hub private or signing keys. Reusable
invitations are the default; single-use invitations authorize one enrollment each, then
atomically rotate to a fresh single-use invitation. Only single-use invitation secrets
are retained in the hub's private authorization file; reusable invitation secrets are not.
`musubi status` never shows invitation secrets. Run `musubi hub invite --single-use` locally to
create and print a new single-use invitation; network clients cannot retrieve invitation
secrets.
Revoking an invitation prevents new enrollments without revoking existing clients. Revoking a
client certificate ends its connections and refuses reconnects. Revoke invitations it knows
too, to prevent re-enrollment. TLS separately bounds handshakes, anonymous enrollment and
authenticated sessions; authentication and enrollment share one ten-second deadline. If the
hub cannot read valid authorization, it closes TLS sessions and pauses TLS admission until the
file recovers, while local-socket and ssh service continue. There is no plaintext network mode.
