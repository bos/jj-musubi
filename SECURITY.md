# Security

Report a vulnerability privately, through
[GitHub](https://github.com/bos/jj-musubi/security/advisories/new), not in a public issue.
Only the latest release gets fixes.

## What musubi protects

Anyone who can reach a hub can read and write every hive on it. So a hub listens only on a
local socket that only its own user can reach, and other machines come in over ssh, as that
user, with a key allowed only to run `musubi hub connect`.
