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

The renderer takes display names and descriptions from `catalog.json`, so a saved measurement
can use current UI copy. Categories absent from the current catalog keep their saved labels.
The source commit recorded by a snapshot is displayed in place of its temporary capture
workspace's revision.

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
Labels appear selectively to avoid collisions. Hovering a node highlights its connections
and shows a small name and coverage tooltip. Hovering an arrow compares coverage at both ends,
using the same selected techniques and replay position. Tooltips are translucent with a blurred
backdrop. Clicking keeps the emphasis and opens
the full coverage chart; hovering alone never opens it. Geometric hit testing distinguishes
circles, arrows and group boundaries. Info boxes open in a corner of the graph and stay inside
it, scrolling when needed. Only dragging a box gives it a position away from the corners.
Pattern fills move and scale with their circles. The embedded view saves filters, expansion
and pinned-chart positions.
Double-clicking a collapsed crate expands its modules without zooming; double-clicking a module
focuses it. Control menus overlay the graph, leaving the toolbar and canvas fixed. The toolbar
keeps its expand/collapse toggle and crate/module counts in fixed-width slots.

For each line and technique, the dataset stores the first event that reached it. Scrubbing
changes the event cutoff and recomputes the union. Coverage changes only at recorded test or
fuzz-checkpoint completions. Replay spans eight seconds from start to finish in elapsed run time
or summed run durations. Switching clocks preserves the current event position.

The embedded view uses the host's tooltip handling. Offline pages include
`standalone-tooltips.js` for hover and keyboard-focus tooltips, including explanations on
disabled replay controls. The interaction instructions are under **Explore the code**.

[Reproducing the network](assurance.md) covers collection and rendering commands.

Clicking an import arrow opens one compact comparison with adjacent overall-coverage bars.
**Compare techniques** opens paired bars for each technique, using the same styling and scale
as ordinary node charts. One close action dismisses the connection. Clicking an endpoint name
opens its ordinary chart. The import-path count appears inside the comparison’s details.

The footer’s short source commit links to that commit’s tree on GitHub.
