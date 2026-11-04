# Code reviews

What a review of a change to musubi looks for, and how to run one.
[AGENTS.md](../../AGENTS.md) says who reviews and what checks run first.

## How to run one

Split a change's risks among a few reviewers, two to four, working at once, each with one or
two of the lenses below, reporting at most six findings in a few sentences each. A reviewer
reads the diff and the code around it, and doesn't repeat the author's checks. Run one targeted
test only when establishing a specific finding depends on it, and say which one and why.

Choose the lenses by what the change touches:

- the protocol, translation, realization, the canonical store, or how concurrent changes
  resolve: **correctness**;
- a command, flag, setting, message, hint, help text, or the user guide: **what users see**;
- tests: **tests**;
- a path that runs often, on every operation or every sync: **cost**.

A change to a command usually needs both of the first two.

## Correctness

Read [design.md](design.md) before reviewing a change to what musubi does. Trace the change
through each machine's repository, the hub, and the other machines: what each holds before,
during and after, and what a crash at each step leaves. A change that must hold over every
interleaving belongs in the Lean model first ([testing-philosophy.md](testing-philosophy.md)
says what each kind of change needs).

Above all, look for:

- work lost, or a working copy changed, on any machine;
- a concurrent change on two machines resolving otherwise than jj resolves it on one
  ([races.md](races.md));
- a refusal or a failure that leaves a repository in a state no command in the guide gets
  it out of;
- a check that the model assumes of the code and that the code no longer does.

Challenge the dependencies and test doubles along that path: which error, panic, changing answer
between calls, or partial effect does a double make impossible? Trace the supported contract
through the real dependency's documentation and implementation, including what can already have
changed when a call fails. Show how the production path can reach the suspected failure; an
arbitrary violation of a trait's contract isn't evidence of a supported state. Keep faults within
[testing-philosophy.md, "What is in scope"](testing-philosophy.md#what-is-in-scope).

For a suspected correctness bug, provide or ask for a small failing reproducer or a concrete
trace where feasible: the starting state, calls and effects, and the guarantee broken. For the
resulting fix, the author shows that the reproducer fails before it and passes after it. When
execution is impractical, say why and give a precise analytical argument. Use the narrowest
existing test layer that exposes the bug; a review comment doesn't by itself require a new
expensive test. Follow [testing-philosophy.md](testing-philosophy.md) for any test added.

## What users see

Read the change as someone who knows jj, git and ssh, and nothing of musubi's design, meeting
it on the first day. [docs/AGENTS.md](../AGENTS.md) holds the vocabulary, and says what
commands print.

Run through the commands the change touches as a user would, from the
[quick start](../../README.md#quick-start) and the
[setup guide](../guides/setup.md): read what each prints, in the snapshots of
`crates/musubi/tests/cli.rs` or in the code that prints it. Look for:

- output nobody asked for: narration, settings, defaults and hints the user needn't act on,
  against [docs/AGENTS.md, "What commands print"](../AGENTS.md#what-commands-print);
- missing progress while a command waits on a sync in a terminal, or progress left behind
  afterwards or printed to a non-terminal;
- an error longer than a line and a hint, or one that explains musubi rather than saying what
  went wrong and the command to run;
- a step that doesn't work as the guide says, or that depends on something the guide doesn't
  mention: the current directory, a variable, a file left by an earlier step, ssh to this
  machine itself;
- words from the design (node, canonical, realization, bundle) or internal ids in what users
  see;
- the help, the guide, the reference, the troubleshooting page and the snapshots disagreeing
  with each other or with what the code does;
- a message a user acts on that the troubleshooting page doesn't list.

Read changes to `the_quick_start_works_as_written` as a first session, checking the commands
and their output against the quick start.
[Testing philosophy](testing-philosophy.md#what-each-kind-of-change-needs) says when to update it.

## Tests

Follow [testing-philosophy.md](testing-philosophy.md): name what each test protects, check that
nothing covers it already at another layer, and that the commit says what breaking makes it
fail ([testing-philosophy.md, "Showing that a test
works"](testing-philosophy.md#showing-that-a-test-works)). Check that a snapshot shows nothing
that varies from run to run, and that a test reaches no real machine.

## Cost

Look for work repeated on a path that runs often: jj commands, history walks, ssh connections,
reads and writes of files whose contents haven't changed.
[AGENTS.md, "Resilience"](../../AGENTS.md#resilience) says how to write files on such a path.
