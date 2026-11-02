# The assurance renderer

The assurance renderer turns recorded runs and Rust source structure into an interactive
code map. Proof scope, line coverage and mutation results use different marks because they
measure different things.

## Data and layout

Python prepares a frozen JSON dataset.
[build.py](../../contrib/assurance/build.py) joins run observations to the source graph and
curated proof links. [render.py](../../contrib/assurance/render.py) bundles a compact subset
with HTML, CSS and JavaScript as an inline fragment or an offline page. Detailed run records
remain in the full dataset.

[graph.py](../../contrib/assurance/graph.py) resolves Rust imports and computes a force layout
with sorted identities, a fixed seed and a fixed iteration count. Crate anchors keep each
group together. The browser reuses the saved coordinates, so filtering and replay leave the
layout undisturbed. Larger circles represent crates, which expand independently into module
circles. Imports are combined between visible nodes; a convex hull outlines each expanded
crate. Modules without compiler coverage mappings are omitted. Measured zero coverage stays
visible.

## Reading the marks

Arrows show source dependencies, with thickness counting distinct import paths. A rim
identifies a module's role; outgoing arrows use that role's colour. Small symbols identify
proof and test scopes. Pie slices show executable Rust lines reached by the enabled
techniques. Each shared line counts once in the union and is split equally among its
techniques' slices. Popup bars show each technique's full reach, including overlaps.

Conformance tests are identified by calls to the Lean oracle; the Kani overlay uses related
Rust tests. Mutation results count edited programs that failed tests, passed, failed to
compile or timed out. They contribute no line-coverage percentage. Missing run data stays
distinct from zero.

## Drawing and interaction

[network-view.js](../../contrib/assurance/network-view.js) draws the graph on Canvas. HTML
provides controls and draggable, pinnable info boxes. Separate canvas layers blur background
edges inside unselected circles while active arrows stay sharp above them, with a pale halo.
Labels appear selectively to avoid collisions. Hovering a node highlights its connections;
clicking keeps that emphasis. Geometric hit testing distinguishes circles, arrows and group
boundaries. The embedded view saves filters, expansion and pinned-chart positions.

For each line and technique, the dataset stores the first event that reached it. Scrubbing
changes the event cutoff and recomputes the union. Coverage changes only at recorded test or
fuzz-checkpoint completions. Replay spans eight seconds from start to finish in elapsed time
or accumulated worker time. Switching clocks preserves the current event position.

[Reproducing the network](assurance.md) covers collection and rendering commands.
