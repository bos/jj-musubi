/-
Executable model of how one machine turns a canonical operation into a native jj operation and
publishes it. `Types` holds the finite observed inputs, `Graph` and `Selectors` compute from
them the source of each parent, the names this machine owns and the prepared base,
`Construction` builds the receipt and the rendered operation, `Steps` runs the phases of an
attempt (capture, preparation, validation, publication, export and cleanup, with recovery), and
`Json` decodes the Rust fixtures that the oracle compares with the model.

Not proved: that native jj behaves as the observations assume, that every reachable state keeps
a safety invariant, and that the Rust code corresponds to the model. See
`docs/internals/conformance.md`, "Native lifecycle inputs and events".
-/
import Musubi.NativeLifecycle.Steps
