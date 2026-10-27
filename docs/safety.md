# How musubi keeps your work safe

A tool that moves history between machines while you rewrite it on all of them has to be
right, every time. A sync that drops a commit, or applies the same rebase twice, is worse than
no sync at all. So musubi was built proof first: its protocol was designed and proved correct
in the Lean theorem prover, its code is checked against that proof, and its tests drive real
jj repositories through the races, crashes and network failures that real machines have.

This page says what musubi promises, and how each promise is checked. The [contributor
docs](internals/README.md) have the full detail.

## What musubi promises

- **Nothing you do is lost.** Every change any machine makes reaches every other machine once
  they can reach the hub. Even if a power cut makes the hub forget its last few minutes, the
  machines still have that work, and send it again.
- **Every machine ends up the same.** Once the machines stop changing things and can reach the
  hub, they all reach the same history, whatever order things happened in.
- **Concurrent changes combine as jj combines them.** Two machines changing the same thing at
  once get exactly what jj makes of two commands run at once on one machine: the same
  divergent change, or the same conflicted bookmark, and nothing worse.
- **No merge is done twice.** When two machines' work crosses, exactly one of them merges it,
  so the hive never ends up with two copies of the same rebase. The one exception is a hub
  that a power cut sets back, after which two machines can merge the same work; nothing is
  lost, and at worst a change is left divergent.
- **A quiet hive stays quiet.** Taking in another machine's work never creates new work to send
  back, so machines don't echo changes at each other.
- **Your files are never touched.** musubi writes only what jj keeps, never your working copy.
- **Losing the hub loses nothing.** Every machine has everything it has seen, so a hub that
  dies is replaced, and fills again from the machines.
- **Leaving costs nothing.** `musubi leave` takes a repository out, and it keeps everything it
  has, its working copy included.

## Designed so that less can go wrong

Much of musubi's safety comes from what it doesn't do.

- **One referee, no negotiation.** The hub decides the order in which machines' updates land,
  with a compare-and-swap: an update is accepted only if it builds on the latest one. When two
  machines send at once, the second is turned away, merges with the first, and sends again.
  There's no voting, and the order of your work never depends on anyone's clock.
- **The hub never merges.** It stores and orders; jj, on the machines, does every merge, with
  the same code that merges concurrent commands on one machine.
- **Everything is checked by its hash.** Commits, trees and operations are named by the hash of
  their contents and checked on arrival. A corrupt message is treated as lost, and sent again.
- **Big transfers resume.** Large objects travel in chunks, and a transfer cut off by a
  dropped connection picks up where it stopped. The whole is checked against its hash before
  anything uses it.
- **What it doesn't understand, it refuses.** An operation from a newer jj, with fields musubi
  doesn't know, is refused rather than passed on with those fields dropped. A machine and a hub
  that speak different versions of the protocol refuse each other, saying so. A `jj op
  abandon` of history other machines have pauses syncing rather than bring the abandoned
  history back.
- **A copy of a copy isn't the copy.** A repository duplicated by copying its directory, by
  hand or by a file-syncing tool, isn't synced as the original, so two repositories never sync
  as one and overwrite each other's working copy.

## Proved in Lean

The sync protocol is modelled in [Lean 4](https://lean-lang.org/), a theorem prover, as a
state machine with any number of machines and a network that loses, duplicates, delays and
reorders messages, and in which any machine can crash at any point, and so can the hub. In
every state that can be reached, Lean checks proofs that:

- the hub only ever moves forward, and anything it has accepted stays accepted;
- the hub has everything its latest state needs, and so does each machine;
- work the hub hasn't accepted is seen only on the machine that made it;
- no two machines ever make the same merge;
- taking in another machine's work never creates new work;
- and once people stop changing things, and the machines' requests and replies get through,
  every machine reaches the hub's history, with every change anyone made in it.

A further model lets the hub go back to an earlier state, as a power cut makes it do. There,
the hub and each machine still have everything their state needs, nothing creates new work,
and once the hub stops going back, the machines fill it in again and reach the same history.
What no longer holds is the rule against duplicate merges, which is why a power cut can leave
a change divergent. That lost or late messages only delay the sync, rather than stop it, is
argued and tested, not proved.

That last is the subtle one: why can't machines keep turning each other away forever? Every
step of the sync lowers a measure with five parts, compared in order: how many machines have
work the hub hasn't taken, how far behind each is, what each is missing, and how many updates
and merges each has pending. A machine that loses a race learns the newer state from the
reply, so it is less far behind; and the hub's state moves at most once for each machine with
work to send. The measure can't fall forever, so the sync ends, and the proof shows it ends
with everyone the same.

Separate models cover the rest of what could go wrong: how each machine's git refs and jj's
import and export of them interact, including `jj undo` and `jj op restore`; which machines'
copies a hive shows as they come and go; which directory on a machine is the copy, and which a
duplicate; and the chunked transfers, whose receiver is proved to put together exactly the
bytes that were sent.

That's more than 400 theorems in all, none left unfinished and no axioms added, and every
proof is checked again on every change. [The Lean model](../formal/README.md) names each
theorem, and lists what the models assume of the code.

## Checking the code against the proof

A proof is only as good as the match between the model and the code. So the model is also a
program: an executable version of it, proved to agree with the model, runs as an oracle in the
tests of musubi's protocol code. Property tests drive musubi's own Rust state machines for the hub
and the machines through generated sequences of user changes, message deliveries, losses,
duplicates, crashes, and a hub that misbehaves, and after every step ask the oracle whether the
model allows it. When the machines settle, the tests also check, step by step, that the measure
from the liveness proof fell.

To check that the checks have teeth, deliberately broken versions of the code are run against
them: a hub that accepts an update without checking that it builds on the latest, a machine
that applies an operation before its parents, a machine that pushes before merging. Each is
caught. `cargo-mutants` makes many more such changes to the hub's and machines' logic
automatically, and the tests are expected to catch every one.
[conformance.md](internals/conformance.md) has the details.

## Every race, with a test

Machines in a hive can run into every race that two jj commands on one machine can, plus a few of
their own: a machine forgets another's workspace while it's building on it, two machines both use
workspace `default`, a commit is rewritten on one machine while another has unsaved edits on top
of it. The [race catalogue](internals/races.md) lists more than 70 of them, each with its outcome,
and each pinned by a test that runs real repositories through the real protocol and hub storage.
The rule throughout is that machines resolve a race exactly as jj resolves it on one machine;
where jj would do something harmful only because the commands came from different machines, musubi
notices and stops.

## A search through real jj

The cases nobody thought of are found by a search. A generated test drives two or three real
repositories with the real `jj` command: commits, rebases, squashes, abandons, undos, commands
run at an older operation, bookmark and tag moves, and workspaces added and forgotten. It moves
branches behind jj's back with `git`, has someone else push to the remote, and fetches and
pushes. It crashes machines partway through a sync, restarts the hub, cuts off the last of the
hub's history as a power cut would, and loses replies.

After every step, every repository must still load, and no git import may undo anything. At
the end, every machine must agree on every commit, change id, bookmark and tag, and every
operation from any machine must be in every machine's history. To tell musubi's mistakes from
jj's own behavior, the test keeps a reference: a jj repository of its own that replays the
hive's history with jj's own merges. Any divergence or conflict the hive has and the reference
doesn't is musubi's doing, and fails the test, as does any rebase done twice.

A failing case shrinks to a small one and replays exactly. The search runs every night with a
new seed.

## Faults and hostile input

- **Flaky links.** A recorded session between two machines is cut at every call, in three ways:
  the request is lost, as when the wifi drops; the request arrives but the reply is lost, as
  when a laptop lid closes just after it went; or the request arrives an hour late. Once the
  link is back, every call must finish as it would have, within a bound.
- **Hostile peers.** The hub is sent requests no honest machine would send: cut short,
  corrupted, spliced together, with made-up ids, or from another protocol version. It must
  answer every one without crashing, and its state may only move forward to states it has
  everything for.
- **Fuzzing.** Coverage-guided fuzzers attack every decoder of what a peer sends: frames,
  messages, bundles of commits, and operations imported from them. Each checks more than that
  nothing crashes: a message that decodes must encode back to one that decodes the same, and
  nothing a fuzzer sends may leave a store holding anything that isn't what its hash says.
- **Torn files.** Files musubi appends to are tested cut off anywhere, zero-filled and
  garbled: each reads back what was written before the damage, or is known to be damaged, and
  never reads as something else.

## Keeping up with jj

musubi links the same jj library the `jj` command does, and works through it rather than
around it. Every night, CI builds musubi against jj's main branch and runs the suite, so a
change in jj that would break musubi shows up before a release brings it. Every change is
tested on Linux, macOS and Windows.

## Read further

- [Design](internals/design.md): what musubi replicates, and why.
- [Sync protocol](internals/protocol.md): what machines and the hub say to each other, and
  the properties that guarantees.
- [The Lean model](../formal/README.md): every theorem, and how the model matches the protocol.
- [Conformance](internals/conformance.md): how the Rust code is checked against the model.
- [Race catalogue](internals/races.md): every race between machines, and its outcome.
- [Testing](internals/testing.md): every layer of tests, and what each guards against.
