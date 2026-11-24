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
detect some transcription errors; they do not make a disclosed phrase safe to share publicly.
The client verifies the hub before disclosing the secret, generates its private key locally, and
proves possession during enrollment. Unauthenticated TLS connections can only attempt enrollment;
they cannot access hives or management operations. Invitations contain no hub private or signing
keys. Reusable invitations are the default; single-use invitations authorize one enrollment
per key, then atomically rotate to a fresh single-use key. Only their secrets are retained in
the hub's private authorization file, so local `musubi status` can show the current keys.
Keep plain status output private on the hub's machine. Templates/JSON omit these keys;
network clients cannot retrieve them.
Revoking an invitation prevents new enrollments without revoking existing clients. Revoking a
client certificate ends its connections and refuses reconnects. Revoke invitations it knows
too, to prevent re-enrollment. There is no plaintext network mode.
