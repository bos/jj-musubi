(() => {
  const root = document.getElementById("musubi-code-network"),
    $ = (s) => root.querySelector(s);
  const data = JSON.parse($("#ng-data").textContent),
    net = data.network,
    nodes = net.nodes;
  const components = net.views.components.nodes.map((id) => nodes[id]),
    componentNames = components.map((n) => n.crate),
    viewCache = new Map();
  const worldPositions = { ...net.views.modules.positions },
    sizeMax = {
      crate: Math.max(...components.map((n) => n.lines)),
      module: Math.max(
        ...Object.values(nodes)
          .filter((n) => n.kind === "module")
          .map((n) => n.lines),
      ),
    };
  for (const c of components)
    worldPositions[c.id] = [0, 1].map(
      (axis) =>
        c.files.reduce((sum, id) => sum + worldPositions[id][axis], 0) /
        c.files.length,
    );
  const mechanisms = Object.fromEntries(data.mechanisms.map((m) => [m.id, m])),
    claims = Object.fromEntries(data.claims.map((c) => [c.id, c])),
    evidence = Object.fromEntries(data.evidence.map((e) => [e.id, e]));
  const roles = Object.fromEntries(data.roles.map((r) => [r.id, r]));
  const roleName = (n) =>
    roles[data.nodeRoles[n.id]]?.name || "Declarations & types";
  const nodeColour = (n) =>
    colours.roles[data.nodeRoles[n.id]] || colours.muted;
  const shapes = {
    diamond: "◆",
    square: "■",
    ring: "◎",
    circle: "●",
    triangle: "▲",
  };
  const esc = (s) =>
    String(s).replace(
      /[&<>"']/g,
      (c) =>
        ({
          "&": "&amp;",
          "<": "&lt;",
          ">": "&gt;",
          '"': "&quot;",
          "'": "&#39;",
        })[c],
    );
  const color = (id) => `var(--viz-series-${mechanisms[id].series})`;
  const measured = data.measured,
    events = measured?.events || [],
    duration = measured?.duration || 1;
  const graphFiles = new Set(Object.keys(measured.files)),
    graphImports = net.imports.filter(
      (e) => graphFiles.has(e.source) && graphFiles.has(e.target),
    ),
    visibleFiles = (c) => c.files.filter((id) => graphFiles.has(id));
  const defaults = {
    version: 5,
    level: "components",
    expanded: [],
    component: componentNames.includes("musubi-sync")
      ? "musubi-sync"
      : componentNames[0],
    selected: null,
    selectedNodes: [],
    selectedEdge: null,
    captureId: measured.captureId,
    enabled: data.mechanisms.map((m) => m.id),
    time: duration,
    clock: "wall",
    focus: null,
    focusScale: 2,
  };
  let state = { ...defaults, selectedNodes: [] },
    cam = { scale: 1, x: 0, y: 0 },
    view,
    screen = {},
    hits = [],
    groupHits = [],
    colours = {},
    width = 0,
    height = 0,
    dpr = 1,
    resizeFrame = null,
    themeFrame = null,
    drawFrame = null,
    gesture = null,
    playing = false,
    playFrame = 0,
    lastTick = 0,
    replayClock = "wall",
    replayPosition = 0,
    hover = null,
    tooltipPoint = null,
    drag = null,
    edgeId = null,
    sourceId = null,
    cameraFrame = 0,
    coverageCache = new Map(),
    coverageKey = "",
    scopeCache = new Map(),
    scopeKey = "",
    markerRects = [],
    inspectors = [],
    preview = null,
    cardDrag = null;
  const edgeLayer = document.createElement("canvas"),
    sharpLayer = document.createElement("canvas"),
    liveLayer = document.createElement("canvas"),
    haloLayer = document.createElement("canvas"),
    haloCtx = haloLayer.getContext("2d"),
    edgeCtx = edgeLayer.getContext("2d"),
    sharpCtx = sharpLayer.getContext("2d"),
    liveCtx = liveLayer.getContext("2d");
  const canvas = $("canvas"),
    ctx = canvas.getContext("2d"),
    tip = $(".tooltip"),
    origin = `ng-${Date.now()}-${Math.random()}`;
  function expansionLevel() {
    return state.expanded.length === 0
      ? "components"
      : state.expanded.length === components.length
        ? "modules"
        : "focus";
  }

  function restore(saved) {
    const x =
      saved?.privateContent?.musubiNetwork ||
      saved?.modelContent?.musubiNetwork;
    if (!x || ![1, 2, 3, 4, 5].includes(x.version)) return false;
    const before = JSON.stringify(state);
    state = Object.fromEntries(
      Object.entries(defaults).map(([key, value]) => [key, x[key] ?? value]),
    );
    if (x.selected === null) state.selected = null;
    state.version = 5;
    if (!nodes["crate:" + state.component])
      state.component = defaults.component;
    if (state.selected !== null && !nodes[state.selected])
      state.selected = null;
    state.expanded = Array.isArray(x.expanded)
      ? componentNames.filter((name) => x.expanded.includes(name))
      : x.level === "modules"
        ? [...componentNames]
        : x.level === "focus"
          ? [state.component]
          : [];
    state.level = expansionLevel();
    const enabled = Array.isArray(x.enabled) ? x.enabled : defaults.enabled;
    state.enabled = data.mechanisms
      .map((m) => m.id)
      .filter(
        (id) =>
          enabled.includes(id) ||
          (id === "conformance" && enabled.includes("lean")) ||
          (enabled.includes("examples") &&
            [
              "unit",
              "integration",
              "races",
              "faults",
              "cli",
              "snapshots",
              "contracts",
              "smoke",
              "compatibility",
            ].includes(id)),
      );
    state.selectedNodes = Array.isArray(x.selectedNodes)
      ? [...new Set(x.selectedNodes.filter((id) => nodes[id]))]
      : state.selected
        ? [state.selected]
        : [];
    state.selected = state.selectedNodes.includes(state.selected)
      ? state.selected
      : state.selectedNodes.at(-1) || null;
    if (Array.isArray(saved?.privateContent?.inspectors))
      inspectors = saved.privateContent.inspectors
        .filter(
          (c) =>
            nodes[c.id] &&
            (nodes[c.id].kind === "crate" || graphFiles.has(c.id)) &&
            Number.isFinite(c.x) &&
            Number.isFinite(c.y),
        )
        .map((c) => ({
          id: c.id,
          x: c.x,
          y: c.y,
          manual: !!c.manual,
          pinned: c.pinned !== false,
        }));
    const box = saved?.privateContent?.selectionBox;
    if (
      box?.id === state.selected &&
      Number.isFinite(box.x) &&
      Number.isFinite(box.y)
    )
      preview = {
        id: box.id,
        x: box.x,
        y: box.y,
        manual: !!box.manual,
        edge: box.edge,
      };
    state.time =
      x.version === 1 || x.captureId !== measured.captureId
        ? duration
        : Math.max(0, Math.min(duration, Number(state.time) || 0));
    state.focusScale =
      x.version < 3
        ? 2
        : Math.max(0.25, Math.min(8, Number(state.focusScale) || 2));
    state.captureId = measured.captureId;
    if (!["wall", "effort"].includes(state.clock)) state.clock = "wall";
    if (!nodes[state.focus]) state.focus = null;
    const changed = JSON.stringify(state) !== before;
    return changed;
  }

  restore(window.openai?.widgetState);
  function persist() {
    if (window.openai?.setWidgetState)
      Promise.resolve(
        window.openai.setWidgetState({
          modelContent: {
            musubiNetwork: { ...state },
            measurement: net.measurement,
            assuranceScope: net.assurance,
            executionRun: measured
              ? {
                  source: measured.sourceRevision,
                  passed: measured.passed,
                  elapsedSeconds: measured.duration,
                }
              : null,
          },
          privateContent: {
            musubiNetwork: { ...state },
            networkOrigin: origin,
            inspectors: inspectors.map(({ id, x, y, manual, pinned }) => ({
              id,
              x,
              y,
              manual: !!manual,
              pinned: !!pinned,
            })),
            selectionBox:
              preview && preview.id === state.selected ? { ...preview } : null,
          },
        }),
      ).catch(() => {});
  }
  window.addEventListener("openai:set_globals", (e) => {
    const g = e.detail?.globals;
    if (
      g?.widgetState &&
      g.widgetState.privateContent?.networkOrigin !== origin
    ) {
      const before = JSON.stringify(inspectors);
      if (restore(g.widgetState)) {
        stop();
        setView();
        render();
      } else if (before !== JSON.stringify(inspectors)) renderInspectors();
    }
    if (g?.visualizationStyleVariables || g?.visualizationTheme || g?.theme)
      scheduleTheme();
  });
  function active(e) {
    return state.enabled.includes(e.mechanism);
  }
  function scopeKinds(n) {
    if (!scopeCache.has(n.id))
      scopeCache.set(
        n.id,
        data.mechanisms
          .filter((m) =>
            n.claims.some((id) =>
              claims[id].evidence.some(
                (eid) =>
                  evidence[eid].mechanism === m.id && active(evidence[eid]),
              ),
            ),
          )
          .map((m) => m.id),
      );
    return scopeCache.get(n.id);
  }
  function fileCoverage(id) {
    if (coverageCache.has(id)) return coverageCache.get(id);
    const file = measured?.files[id],
      result = {
        total: file?.lines.length || 0,
        hit: 0,
        kinds: [],
        byKind: {},
        credit: {},
        unmeasured: !file,
      };
    if (file) {
      const selected = state.enabled.filter((m) => file.first[m]),
        cutoff = events.reduce((n, e, i) => (e.t <= state.time ? i + 1 : n), 0);
      for (let i = 0; i < file.lines.length; i++) {
        const found = selected.filter(
          (m) => file.first[m][i] && file.first[m][i] <= cutoff,
        );
        if (found.length) {
          result.hit++;
          for (const m of found) {
            result.byKind[m] = (result.byKind[m] || 0) + 1;
            result.credit[m] = (result.credit[m] || 0) + 1 / found.length;
            if (!result.kinds.includes(m)) result.kinds.push(m);
          }
        }
      }
    }
    coverageCache.set(id, result);
    return result;
  }
  function execution(n) {
    if (n.kind !== "crate") return fileCoverage(n.id);
    if (coverageCache.has(n.id)) return coverageCache.get(n.id);
    const parts = n.files.map(fileCoverage),
      byKind = {},
      credit = {};
    for (const c of parts) {
      for (const [m, hit] of Object.entries(c.byKind))
        byKind[m] = (byKind[m] || 0) + hit;
      for (const [m, value] of Object.entries(c.credit))
        credit[m] = (credit[m] || 0) + value;
    }
    const result = {
      total: parts.reduce((s, c) => s + c.total, 0),
      hit: parts.reduce((s, c) => s + c.hit, 0),
      kinds: Object.keys(byKind),
      byKind,
      credit,
      unmeasured: parts.every((c) => c.unmeasured),
    };
    coverageCache.set(n.id, result);
    return result;
  }
  function mutationStats(n) {
    const result = { noticed: 0, missed: 0, unviable: 0, timeout: 0 };
    for (const id of n.kind === "crate" ? n.files : [n.id])
      for (const [key, value] of Object.entries(
        measured.mutation?.files[id] || {},
      ))
        result[key] = (result[key] || 0) + value;
    return result;
  }
  function mutationText(n) {
    const r = n
      ? mutationStats(n)
      : Object.values(measured.mutation?.files || {}).reduce(
          (a, r) => {
            for (const k of ["noticed", "missed", "unviable", "timeout"])
              a[k] = (a[k] || 0) + (r[k] || 0);
            return a;
          },
          { noticed: 0, missed: 0, unviable: 0, timeout: 0 },
        );
    return Object.values(r).some(Boolean)
      ? `${r.noticed} ${r.noticed === 1 ? "mutation" : "mutations"} caught by tests; ${r.missed} survived. ${r.unviable} failed to compile; ${r.timeout} timed out.`
      : measured.mutation?.sites?.length
        ? "No mutations tried for this selection."
        : "No mutation results recorded.";
  }
  function mutationOnly() {
    return state.enabled.length === 1 && state.enabled[0] === "mutation";
  }
  function nodeKinds(n) {
    return [...new Set([...scopeKinds(n), ...execution(n).kinds])];
  }

  function expandedView() {
    const key = state.expanded.join("|");
    if (viewCache.has(key)) return viewCache.get(key);
    const ids = components.flatMap((c) =>
        state.expanded.includes(c.crate) ? visibleFiles(c) : [c.id],
      ),
      visible = new Set(ids),
      links = new Map(),
      mapped = (id) => (visible.has(id) ? id : "crate:" + nodes[id].crate);
    for (const item of graphImports) {
      const source = mapped(item.source),
        target = mapped(item.target);
      if (source === target) continue;
      const id = source + ">" + target;
      if (!links.has(id))
        links.set(id, { id, source, target, weight: 0, imports: [] });
      const edge = links.get(id);
      edge.weight++;
      edge.imports.push(item.id);
    }
    const result = {
      nodes: ids,
      links: [...links.values()],
      positions: worldPositions,
    };
    viewCache.set(key, result);
    return result;
  }
  function setView({ resetCamera = true } = {}) {
    cancelAnimationFrame(cameraFrame);
    view = expandedView();
    const visible = new Set(view.nodes),
      represent = (id) => {
        if (visible.has(id)) return id;
        if (!id || !nodes[id]) return null;
        const parent = "crate:" + nodes[id].crate;
        return nodes[id].kind === "module" && visible.has(parent)
          ? parent
          : null;
      };
    state.selectedNodes = [
      ...new Set(state.selectedNodes.map(represent).filter(Boolean)),
    ];
    state.selected =
      represent(state.selected) || state.selectedNodes.at(-1) || null;
    if (state.selected && !state.selectedNodes.includes(state.selected))
      state.selectedNodes.push(state.selected);
    if (!visible.has(state.focus)) state.focus = null;
    if (resetCamera) cam = { scale: 1, x: 0, y: 0 };
    edgeId = view.links.some((e) => e.id === state.selectedEdge)
      ? state.selectedEdge
      : null;
    state.selectedEdge = edgeId;
    hover = null;
    sourceId = null;
    tip.hidden = true;
    hidePreview();
    if (resetCamera && state.focus && width) cam = focusCamera(state.focus);
  }
  function readColours() {
    const p = document.createElement("span");
    root.append(p);
    const resolve = (v) => {
      p.style.color = v;
      return getComputedStyle(p).color;
    };
    colours = {
      fg: resolve("var(--foreground)"),
      muted: resolve("var(--muted-foreground)"),
      border: resolve("var(--border)"),
      bg: resolve("var(--background)"),
      surface: resolve("var(--muted)"),
      coverage: resolve("var(--viz-series-1)"),
      context: resolve(
        "color-mix(in srgb,var(--foreground) 45%,var(--background))",
      ),
      halo: resolve(
        "color-mix(in srgb,var(--background) 92%,var(--foreground))",
      ),
      series: {},
    };
    for (const m of data.mechanisms)
      colours.series[m.id] = resolve(color(m.id));
    const sample = document.createElement("canvas").getContext("2d"),
      luminance = (value) => {
        sample.fillStyle = value;
        sample.fillRect(0, 0, 1, 1);
        const rgb = [...sample.getImageData(0, 0, 1, 1).data]
          .slice(0, 3)
          .map((v) => {
            const x = v / 255;
            return x <= 0.04045 ? x / 12.92 : ((x + 0.055) / 1.055) ** 2.4;
          });
        return rgb[0] * 0.2126 + rgb[1] * 0.7152 + rgb[2] * 0.0722;
      },
      background = luminance(colours.bg),
      contrast = (value) => {
        const l = luminance(value);
        return (
          (Math.max(l, background) + 0.05) / (Math.min(l, background) + 0.05)
        );
      };
    colours.roles = Object.fromEntries(
      data.roles.map((r) => {
        const base = r.series
          ? resolve(`var(--viz-series-${r.series})`)
          : colours.muted;
        let value = base;
        for (let mix = 5; contrast(value) < 3.25 && mix <= 100; mix += 5)
          value = resolve(
            `color-mix(in srgb,${base} ${100 - mix}%,var(--foreground))`,
          );
        const key = root.querySelector(`[data-role="${r.id}"]`);
        if (key) key.style.background = value;
        return [r.id, value];
      }),
    );
    colours.nodeBorders = Object.fromEntries(
      [...data.roles.map((r) => r.id), "declarations"].map((id) => [
        id,
        resolve(
          `color-mix(in srgb,${colours.roles[id] || colours.muted} 55%,var(--foreground))`,
        ),
      ]),
    );
    colours.fills = {};
    for (const m of data.mechanisms) {
      if (m.pattern === "solid") {
        colours.fills[m.id] = colours.series[m.id];
        continue;
      }
      const tile = document.createElement("canvas");
      tile.width = tile.height = 8;
      const c = tile.getContext("2d");
      c.fillStyle = colours.series[m.id];
      c.fillRect(0, 0, 8, 8);
      c.strokeStyle = c.fillStyle = colours.bg;
      c.globalAlpha = 0.65;
      if (m.pattern === "backstripes") {
        c.translate(8, 0);
        c.scale(-1, 1);
      }
      c.lineWidth = 2;
      c.beginPath();
      c.moveTo(-2, 2);
      c.lineTo(2, -2);
      c.moveTo(0, 8);
      c.lineTo(8, 0);
      c.moveTo(6, 10);
      c.lineTo(10, 6);
      c.stroke();
      colours.fills[m.id] = ctx.createPattern(tile, "repeat");
    }
    p.remove();
  }
  function scheduleTheme() {
    if (themeFrame !== null) return;
    themeFrame = requestAnimationFrame(() => {
      themeFrame = null;
      readColours();
      draw();
    });
  }
  function resize() {
    const w = $(".board").clientWidth,
      viewport =
        parseFloat(
          getComputedStyle(root).getPropertyValue(
            "--assurance-viewport-height",
          ),
        ) || window.innerHeight,
      chrome =
        root.getBoundingClientRect().height -
        $(".board").getBoundingClientRect().height,
      body = getComputedStyle(document.body),
      h = Math.round(
        Math.max(
          200,
          Math.min(
            440,
            viewport -
              chrome -
              parseFloat(body.marginTop) -
              parseFloat(body.marginBottom) -
              32,
          ),
        ),
      ),
      r = Math.min(2, window.devicePixelRatio || 1);
    if (w <= 0 || (w === width && h === height && r === dpr)) return;
    width = w;
    height = h;
    dpr = r;
    canvas.width = Math.round(w * r);
    canvas.height = Math.round(h * r);
    canvas.style.height = h + "px";
    if (state.focus) {
      cancelAnimationFrame(cameraFrame);
      cam = focusCamera(state.focus);
    }
    readColours();
    draw();
    renderInspectors();
  }
  function scheduleResize() {
    if (resizeFrame !== null) return;
    resizeFrame = requestAnimationFrame(() => {
      resizeFrame = null;
      resize();
    });
  }
  function graphWidth() {
    return width;
  }
  function layoutBasis() {
    const ps = Object.values(worldPositions),
      xs = ps.map((p) => p[0]),
      ys = ps.map((p) => p[1]),
      minx = Math.min(...xs),
      maxx = Math.max(...xs),
      miny = Math.min(...ys),
      maxy = Math.max(...ys),
      mx = (minx + maxx) / 2,
      my = (miny + maxy) / 2;
    const margin = Math.min(width < 520 ? 48 : 70, height * 0.12),
      fit = Math.min(
        (graphWidth() - margin * 2) / Math.max(1, maxx - minx),
        (height - margin * 2) / Math.max(1, maxy - miny),
      );
    return { mx, my, fit };
  }
  function pointLayout() {
    const { mx, my, fit } = layoutBasis();
    screen = {};
    for (const id of view.nodes) {
      const n = nodes[id],
        p = view.positions[id],
        fraction = Math.sqrt(n.lines / sizeMax[n.kind]);
      screen[id] = {
        x: graphWidth() / 2 + (p[0] - mx) * fit * cam.scale + cam.x,
        y: height / 2 + (p[1] - my) * fit * cam.scale + cam.y,
        r: Math.max(
          4,
          (n.kind === "crate"
            ? Math.min(30, height / 12)
            : Math.min(11, height / 30)) * Math.sqrt(cam.scale),
        ),
      };
    }
  }
  function focusCamera(id) {
    const { mx, my, fit } = layoutBasis(),
      p = view.positions[id],
      scale = state.focusScale;
    return {
      scale,
      x: -(p[0] - mx) * fit * scale,
      y: -(p[1] - my) * fit * scale,
    };
  }
  function moveCamera(target) {
    cancelAnimationFrame(cameraFrame);
    if (matchMedia("(prefers-reduced-motion: reduce)").matches) {
      cam = target;
      draw();
      return;
    }
    const from = { ...cam },
      started = performance.now();
    function frame(t) {
      const x = Math.min(1, (t - started) / 280),
        k = 1 - Math.pow(1 - x, 3);
      cam = {
        scale: from.scale + (target.scale - from.scale) * k,
        x: from.x + (target.x - from.x) * k,
        y: from.y + (target.y - from.y) * k,
      };
      draw();
      if (x < 1) cameraFrame = requestAnimationFrame(frame);
    }
    cameraFrame = requestAnimationFrame(frame);
  }
  function centerConnections(id) {
    if (!view.nodes.includes(id)) return;
    state.focusScale = 2;
    state.focus = id;
    state.selected = id;
    if (!state.selectedNodes.includes(id)) state.selectedNodes = [id];
    state.component = nodes[id].crate;
    state.selectedEdge = null;
    edgeId = null;
    sourceId = null;
    hover = null;
    tip.hidden = true;
    renderControls();
    renderDetail();
    moveCamera(focusCamera(id));
    persist();
  }
  function wholeNetwork() {
    state.focus = null;
    hover = null;
    tip.hidden = true;
    renderControls();
    moveCamera({ scale: 1, x: 0, y: 0 });
    persist();
  }
  function renderInteraction() {
    const link = focusedEdge(),
      focus =
        nodes[
          state.selected ||
            (!state.selected && hover?.type === "node" ? hover.id : null)
        ],
      text =
        focus?.kind === "crate"
          ? `Double-click to expand ${focus.name}`
          : link
            ? `${nodes[link.source].name} → ${nodes[link.target].name} · ${edgeId ? "2 selected · click empty space to clear" : "click to compare endpoints"}`
            : focus
              ? `${state.selectedNodes.length > 1 ? state.selectedNodes.length + " selections" : focus.name} · gray: no direct import link${state.selected ? " · click empty space to clear" : ""}`
              : state.expanded.length
                ? "Double-click a module to focus · empty group space to collapse"
                : "Double-click a crate to expand · scroll to pan · pinch to zoom";
    if ($("#ng-interaction").textContent !== text)
      $("#ng-interaction").textContent = text;
    const key = mutationOnly()
      ? "Markers: mutated modules"
      : link
        ? "Pies: coverage at arrow endpoints"
        : focus
          ? "Pies: selection and import neighbors"
          : "Pies: coverage of selected techniques";
    if ($("#ng-coverage-key").textContent !== key)
      $("#ng-coverage-key").textContent = key;
    $("#ng-coverage-key").dataset.tooltip = mutationOnly()
      ? "Markers locate source files where mutations were tried. Select a crate or module to see its results."
      : "Filled area counts each reached line once across the selected techniques. Shared lines are split equally between slices. Each bar counts that technique's full coverage.";
  }
  function doubleClickNode(id) {
    if (nodes[id].kind === "crate") setExpanded(nodes[id].crate, true);
    else centerConnections(id);
  }
  function hull(points) {
    const sorted = points.slice().sort((a, b) => a.x - b.x || a.y - b.y);
    if (sorted.length < 3) return sorted;
    const cross = (a, b, c) =>
        (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x),
      lo = [],
      hi = [];
    for (const p of sorted) {
      while (lo.length >= 2 && cross(lo.at(-2), lo.at(-1), p) <= 0) lo.pop();
      lo.push(p);
    }
    for (const p of sorted.slice().reverse()) {
      while (hi.length >= 2 && cross(hi.at(-2), hi.at(-1), p) <= 0) hi.pop();
      hi.push(p);
    }
    return lo.slice(0, -1).concat(hi.slice(0, -1));
  }
  function boundaries() {
    groupHits = [];
    if (state.level === "components") return;
    const groups = {};
    for (const id of view.nodes)
      if (nodes[id].kind === "module")
        (groups[nodes[id].crate] ??= []).push(screen[id]);
    ctx.font = `400 ${Math.max(11, parseFloat(getComputedStyle(root).fontSize) * 0.82)}px system-ui`;
    for (const [name, points] of Object.entries(groups)) {
      const expanded = [];
      for (const p of points)
        for (const [dx, dy] of [
          [-1, -1],
          [-1, 1],
          [1, -1],
          [1, 1],
        ])
          expanded.push({ x: p.x + dx * (p.r + 16), y: p.y + dy * (p.r + 16) });
      const poly = hull(expanded);
      if (!poly.length) continue;
      groupHits.push({ type: "group", id: "crate:" + name, crate: name, poly });
      ctx.beginPath();
      ctx.moveTo(poly[0].x, poly[0].y);
      for (const p of poly.slice(1)) ctx.lineTo(p.x, p.y);
      ctx.closePath();
      ctx.fillStyle = colours.fg;
      ctx.globalAlpha = 0.025;
      ctx.fill();
      ctx.globalAlpha = 0.35;
      ctx.strokeStyle = colours.border;
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.globalAlpha = 1;
      const top = poly.reduce((a, b) => (a.y < b.y ? a : b));
      ctx.fillStyle = colours.muted;
      ctx.textAlign = "left";
      ctx.textBaseline = "bottom";
      ctx.fillText(
        name,
        Math.max(4, Math.min(graphWidth() - 140, top.x + 5)),
        Math.max(14, top.y - 5),
      );
    }
  }
  function focusedEdge() {
    return (
      view.links.find(
        (e) =>
          e.id ===
          (edgeId ||
            (!state.selected && hover?.type === "edge" ? hover.id : null)),
      ) || null
    );
  }
  function neighbours(id) {
    return new Set([
      id,
      ...view.links
        .filter((e) => e.source === id || e.target === id)
        .flatMap((e) => [e.source, e.target]),
    ]);
  }
  function drawMethod(id, x, y) {
    const m = mechanisms[id],
      s = 3.5;
    ctx.save();
    ctx.fillStyle = colours.series[id];
    ctx.strokeStyle = colours.series[id];
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    if (m.shape === "square") ctx.rect(x - s, y - s, s * 2, s * 2);
    else if (m.shape === "diamond") {
      ctx.moveTo(x, y - s);
      ctx.lineTo(x + s, y);
      ctx.lineTo(x, y + s);
      ctx.lineTo(x - s, y);
      ctx.closePath();
    } else if (m.shape === "triangle") {
      ctx.moveTo(x, y - s);
      ctx.lineTo(x + s, y + s);
      ctx.lineTo(x - s, y + s);
      ctx.closePath();
    } else ctx.arc(x, y, s, 0, Math.PI * 2);
    if (m.shape === "ring") {
      ctx.stroke();
      ctx.beginPath();
      ctx.arc(x, y, 1, 0, Math.PI * 2);
      ctx.fill();
    } else ctx.fill();
    ctx.restore();
  }
  function drawMethods(id, p, scopes) {
    if (!scopes.length) return;
    const cols = Math.min(4, scopes.length),
      rows = Math.ceil(scopes.length / 4),
      top = p.y - p.r - 10 - (rows - 1) * 9;
    for (const [i, method] of scopes.entries()) {
      const row = Math.floor(i / 4),
        count = Math.min(4, scopes.length - row * 4),
        x = p.x + ((i % 4) - (count - 1) / 2) * 9,
        y = top + row * 9;
      drawMethod(method, x, y);
    }
    const rect = {
      type: "label",
      id,
      x: p.x - (cols - 1) * 4.5 - 5,
      y: top - 5,
      w: (cols - 1) * 9 + 10,
      h: (rows - 1) * 9 + 10,
    };
    markerRects.push(rect);
    hits.push(rect);
  }

  function scheduleDraw() {
    if (drawFrame !== null) return;
    drawFrame = requestAnimationFrame(() => {
      drawFrame = null;
      draw();
    });
  }
  function prepareEdges() {
    for (const layer of [edgeLayer, sharpLayer, liveLayer, haloLayer])
      if (layer.width !== canvas.width || layer.height !== canvas.height) {
        layer.width = canvas.width;
        layer.height = canvas.height;
      }
    edgeCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    edgeCtx.clearRect(0, 0, width, height);
    liveCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    liveCtx.clearRect(0, 0, width, height);
    haloCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    haloCtx.clearRect(0, 0, width, height);
    haloCtx.strokeStyle = haloCtx.fillStyle = colours.halo;
    haloCtx.globalAlpha = 1;
    haloCtx.lineCap = haloCtx.lineJoin = "round";
  }
  function arrowHead(c, end, ux, uy, size) {
    c.beginPath();
    c.moveTo(end.x, end.y);
    c.lineTo(
      end.x - ux * size - uy * size * 0.55,
      end.y - uy * size + ux * size * 0.55,
    );
    c.lineTo(
      end.x - ux * size + uy * size * 0.55,
      end.y - uy * size - ux * size * 0.55,
    );
    c.closePath();
  }
  function nodePath(c, p) {
    c.moveTo(p.x + p.r, p.y);
    c.arc(p.x, p.y, p.r, 0, Math.PI * 2);
  }
  function paintConnections() {
    const soft = view.nodes.filter((id) => !state.selectedNodes.includes(id));
    sharpCtx.setTransform(1, 0, 0, 1, 0, 0);
    sharpCtx.clearRect(0, 0, sharpLayer.width, sharpLayer.height);
    sharpCtx.drawImage(edgeLayer, 0, 0);
    sharpCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    sharpCtx.globalCompositeOperation = "destination-out";
    sharpCtx.beginPath();
    for (const id of soft) {
      const p = screen[id];
      nodePath(sharpCtx, p);
    }
    sharpCtx.fill();
    sharpCtx.globalCompositeOperation = "source-over";
    ctx.globalAlpha = 1;
    ctx.drawImage(sharpLayer, 0, 0, width, height);
    if (!soft.length) return;
    ctx.save();
    ctx.beginPath();
    for (const id of soft) {
      const p = screen[id];
      nodePath(ctx, p);
    }
    ctx.clip();
    ctx.filter = `blur(${1.5 * dpr}px)`;
    ctx.drawImage(edgeLayer, 0, 0, width, height);
    ctx.restore();
  }
  function limitPan() {
    const ps = Object.values(screen);
    if (!ps.length) return false;
    const left = Math.min(...ps.map((p) => p.x - p.r)),
      right = Math.max(...ps.map((p) => p.x + p.r)),
      top = Math.min(...ps.map((p) => p.y - p.r)),
      bottom = Math.max(...ps.map((p) => p.y + p.r)),
      keep = Math.sqrt(0.05),
      kx = Math.min(graphWidth(), right - left) * keep,
      ky = Math.min(height, bottom - top) * keep;
    let dx = Math.max(kx - right, Math.min(graphWidth() - kx - left, 0)),
      dy = Math.max(ky - bottom, Math.min(height - ky - top, 0));
    const visible = ps.some((p) => {
      const x = p.x + dx,
        y = p.y + dy;
      return (
        Math.hypot(
          x - Math.max(0, Math.min(graphWidth(), x)),
          y - Math.max(0, Math.min(height, y)),
        ) < p.r
      );
    });
    if (!visible) {
      let nearest = null;
      for (const p of ps) {
        const px = Math.min(graphWidth() / 2, p.r + 12),
          py = Math.min(height / 2, p.r + 12),
          x = p.x + dx,
          y = p.y + dy,
          sx = Math.max(px, Math.min(graphWidth() - px, x)) - x,
          sy = Math.max(py, Math.min(height - py, y)) - y,
          d = sx * sx + sy * sy;
        if (!nearest || d < nearest.d) nearest = { sx, sy, d };
      }
      dx += nearest.sx;
      dy += nearest.sy;
    }
    if (Math.abs(dx) + Math.abs(dy) < 0.001) return false;
    cam.x += dx;
    cam.y += dy;
    if (drag?.moved) {
      drag.baseX = cam.x;
      drag.baseY = cam.y;
      drag.x = drag.lastX;
      drag.y = drag.lastY;
    }
    return true;
  }
  function draw() {
    if (drawFrame !== null) {
      cancelAnimationFrame(drawFrame);
      drawFrame = null;
    }
    if (!width || !view) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);
    pointLayout();
    if (limitPan()) pointLayout();
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, 0, graphWidth(), height);
    ctx.clip();
    boundaries();
    hits = [];
    markerRects = [];
    const link = focusedEdge(),
      highlighted = state.selectedNodes.length
        ? state.selectedNodes
        : link
          ? [link.source, link.target]
          : hover?.type === "node"
            ? [hover.id]
            : [],
      near = link
        ? new Set(highlighted)
        : highlighted.length
          ? new Set(highlighted.flatMap((id) => [...neighbours(id)]))
          : null,
      maxWeight = Math.max(1, ...view.links.map((e) => e.weight));
    ctx.fillStyle = colours.bg;
    ctx.globalAlpha = 1;
    ctx.beginPath();
    for (const id of view.nodes) nodePath(ctx, screen[id]);
    ctx.fill();
    prepareEdges();
    {
      for (const e of view.links) {
        const a = screen[e.source],
          b = screen[e.target],
          focused =
            e.id === edgeId ||
            (!state.selected && hover?.type === "edge" && hover.id === e.id),
          related = link
            ? focused
            : highlighted.includes(e.source) || highlighted.includes(e.target),
          ctx = focused || related ? liveCtx : edgeCtx;
        const dx = b.x - a.x,
          dy = b.y - a.y,
          d = Math.max(1, Math.hypot(dx, dy)),
          start = {
            x: a.x + (dx / d) * (a.r + 3),
            y: a.y + (dy / d) * (a.r + 3),
          },
          end = {
            x: b.x - (dx / d) * (b.r + 5),
            y: b.y - (dy / d) * (b.r + 5),
          };
        ctx.strokeStyle =
          near && !related && !focused
            ? colours.context
            : nodeColour(nodes[e.source]);
        ctx.lineWidth =
          near && !related && !focused
            ? 0.9
            : 0.65 + (3 * Math.log1p(e.weight)) / Math.log1p(maxWeight);
        ctx.globalAlpha = focused
          ? 1
          : related
            ? 0.95
            : near
              ? 0.5
              : state.expanded.length
                ? 0.38
                : 0.42;
        ctx.beginPath();
        ctx.moveTo(start.x, start.y);
        ctx.lineTo(end.x, end.y);
        ctx.stroke();
        if (focused || related) {
          const size = 4 + ctx.lineWidth;
          haloCtx.lineWidth = ctx.lineWidth + 2.4;
          haloCtx.beginPath();
          haloCtx.moveTo(start.x, start.y);
          haloCtx.lineTo(end.x, end.y);
          haloCtx.stroke();
          arrowHead(haloCtx, end, dx / d, dy / d, size);
          haloCtx.lineWidth = 2.4;
          haloCtx.fill();
          haloCtx.stroke();
          arrowHead(ctx, end, dx / d, dy / d, size);
          ctx.fillStyle = ctx.strokeStyle;
          ctx.fill();
        }
        hits.push({ type: "edge", id: e.id, a: start, b: end, r: 6 });
      }
    }
    paintConnections();
    for (const id of view.nodes) {
      const n = nodes[id],
        p = screen[id],
        scopes = scopeKinds(n),
        run = execution(n),
        contextOnly =
          (!!near && !near.has(id)) ||
          (mutationOnly() && !Object.values(mutationStats(n)).some(Boolean)),
        activeNode =
          state.selectedNodes.includes(id) ||
          (!state.selected && hover?.type === "node" && hover.id === id),
        opacity = activeNode ? 1 : near ? 0.95 : 0.9;
      if (contextOnly) {
        ctx.globalAlpha = 1;
        ctx.strokeStyle = colours.context;
        ctx.lineWidth = 1;
        ctx.beginPath();
        nodePath(ctx, p);
        ctx.stroke();
        hits.push({
          type: "node",
          id,
          x: p.x,
          y: p.y,
          r: Math.max(14, p.r + 7),
        });
        continue;
      }
      ctx.globalAlpha = opacity;
      ctx.fillStyle = colours.bg;
      ctx.beginPath();
      nodePath(ctx, p);
      if (state.selectedNodes.includes(id)) ctx.fill();
      ctx.fillStyle = nodeColour(n);
      ctx.globalAlpha = opacity * 0.1;
      ctx.fill();
      ctx.globalAlpha = opacity;
      ctx.strokeStyle = colours.nodeBorders[data.nodeRoles[n.id]];
      ctx.lineWidth = activeNode ? 2 : 1;
      ctx.beginPath();
      nodePath(ctx, p);
      ctx.stroke();
      let angle = -Math.PI / 2;
      const fillScale = p.r / (n.kind === "crate" ? 30 : 11),
        fillTransform = new DOMMatrix([fillScale, 0, 0, fillScale, p.x, p.y]);
      for (const method of data.mechanisms) {
        const value = run.credit[method.id] || 0;
        if (!value) continue;
        const end = angle + (Math.PI * 2 * value) / Math.max(1, run.total);
        const fill = colours.fills[method.id];
        // Keep the texture attached to the circle as its centre and radius change.
        if (fill instanceof CanvasPattern) fill.setTransform(fillTransform);
        ctx.fillStyle = fill;
        ctx.globalAlpha = opacity * 0.9;
        ctx.beginPath();
        ctx.moveTo(p.x, p.y);
        ctx.arc(p.x, p.y, p.r - 1, angle, end);
        ctx.closePath();
        ctx.fill();
        angle = end;
      }
      ctx.globalAlpha = opacity;
      drawMethods(id, p, scopes);
      hits.push({ type: "node", id, x: p.x, y: p.y, r: Math.max(14, p.r + 7) });
    }
    ctx.globalAlpha = 1;
    if (highlighted.length || edgeId || hover?.type === "edge") {
      ctx.save();
      ctx.filter = `blur(${0.7 * dpr}px)`;
      ctx.drawImage(haloLayer, 0, 0, width, height);
      ctx.restore();
    }
    ctx.drawImage(liveLayer, 0, 0, width, height);
    drawFocus(highlighted);
    drawLabels(near);
    renderInteraction();
    ctx.restore();
    positionCards();
    renderHoverTooltip();
  }

  function drawFocus(ids) {
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = colours.fg;
    ctx.lineWidth = 2;
    ctx.beginPath();
    for (const id of ids) {
      const p = screen[id];
      if (!p) continue;
      const r = p.r + 4,
        l = 5;
      for (const sx of [-1, 1])
        for (const sy of [-1, 1]) {
          const x = p.x + sx * r,
            y = p.y + sy * r;
          ctx.moveTo(x - sx * l, y);
          ctx.lineTo(x, y);
          ctx.lineTo(x, y - sy * l);
        }
    }
    ctx.stroke();
    ctx.restore();
  }
  function drawLabels(near) {
    const font = Math.max(
        11,
        parseFloat(getComputedStyle(root).fontSize) * 0.88,
      ),
      line = font * 1.5;
    ctx.font = `400 ${font}px system-ui`;
    ctx.textBaseline = "middle";
    const link = focusedEdge(),
      primary = new Set(
        state.selectedNodes.length
          ? state.selectedNodes
          : link
            ? [link.source, link.target]
            : hover?.type === "node"
              ? [hover.id]
              : [],
      ),
      neighbourWeights = new Map();
    for (const e of view.links) {
      if (primary.has(e.source) && !primary.has(e.target))
        neighbourWeights.set(
          e.target,
          (neighbourWeights.get(e.target) || 0) + e.weight,
        );
      if (primary.has(e.target) && !primary.has(e.source))
        neighbourWeights.set(
          e.source,
          (neighbourWeights.get(e.source) || 0) + e.weight,
        );
    }
    const labelledNeighbours = new Set(
      (link ? [] : [...neighbourWeights])
        .sort((a, b) => b[1] - a[1])
        .slice(0, 4)
        .map(([id]) => id),
    );
    const strength = (id) =>
      view.links
        .filter((e) => e.source === id || e.target === id)
        .reduce((n, e) => n + e.weight, 0);
    const ordered = view.nodes
        .slice()
        .sort(
          (a, b) =>
            primary.has(b) - primary.has(a) ||
            (nodes[b].kind === "crate") - (nodes[a].kind === "crate") ||
            strength(b) - strength(a),
        ),
      rects = [
        ...markerRects.map((r) => ({ ...r })),
        ...view.nodes.map((id) => {
          const p = screen[id];
          return {
            x: p.x - p.r - 3,
            y: p.y - p.r - 3,
            w: p.r * 2 + 6,
            h: p.r * 2 + 6,
          };
        }),
      ];
    for (const id of ordered) {
      const n = nodes[id],
        p = screen[id],
        essential = n.kind === "crate" || primary.has(id),
        interesting = essential || labelledNeighbours.has(id);
      if (!interesting) continue;
      const text = n.name,
        extra = n.kind === "crate" ? n.label : null,
        w =
          Math.max(
            ctx.measureText(text).width,
            extra ? ctx.measureText(extra).width : 0,
          ) + 8,
        h = extra ? line * 2 : line;
      const distances = primary.has(id)
          ? [14, 32, 56, 88]
          : labelledNeighbours.has(id)
            ? [10, 30, 54, 82]
            : [10],
        candidates = distances.flatMap((d) => [
          [p.x - w / 2, p.y + p.r + d],
          [p.x - w / 2, p.y - p.r - d - h],
          [p.x + p.r + d, p.y - h / 2],
          [p.x - p.r - d - w, p.y - h / 2],
        ]);
      const good = candidates.find(
        ([x, y]) =>
          x >= 3 &&
          x + w <= graphWidth() - 3 &&
          y >= 3 &&
          y + h <= height - 3 &&
          !rects.some(
            (r) =>
              x < r.x + r.w + 4 &&
              x + w + 4 > r.x &&
              y < r.y + r.h + 3 &&
              y + h + 3 > r.y,
          ),
      );
      if (!good) continue;
      const [x, y] = good;
      rects.push({ x, y, w, h });
      hits.push({ type: "label", id, x, y, w, h });
      ctx.globalAlpha = 1;
      if (primary.has(id) || labelledNeighbours.has(id)) {
        const tx = Math.max(x, Math.min(x + w, p.x)),
          ty = Math.max(y, Math.min(y + h, p.y)),
          dx = tx - p.x,
          dy = ty - p.y,
          d = Math.max(1, Math.hypot(dx, dy));
        ctx.strokeStyle = primary.has(id) ? colours.fg : colours.context;
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(p.x + (dx / d) * (p.r + 6), p.y + (dy / d) * (p.r + 6));
        ctx.lineTo(tx, ty);
        ctx.stroke();
      }
      ctx.fillStyle = colours.bg;
      ctx.fillRect(x - 1, y - 2, w + 2, h + 4);
      ctx.textAlign = "left";
      ctx.fillStyle = colours.fg;
      ctx.fillText(text, x + 4, y + line * 0.5);
      if (extra) {
        ctx.fillStyle = colours.muted;
        ctx.fillText(extra, x + 4, y + line * 1.5);
      }
      ctx.globalAlpha = 1;
    }
  }
  function symbol(id, on = true) {
    return `<span class="symbol" style="color:${on ? color(id) : "var(--muted-foreground)"}" aria-hidden="true">${shapes[mechanisms[id].shape]}</span>`;
  }
  function fillStyle(id) {
    const m = mechanisms[id],
      pattern =
        m.pattern !== "solid"
          ? `repeating-linear-gradient(${m.pattern === "backstripes" ? 45 : 135}deg,transparent 0 3px,var(--background) 3px 4px)`
          : "none";
    return `background-color:${color(id)};background-image:${pattern};background-size:8px 8px`;
  }
  function swatch(id) {
    return `<span class="pie-key" style="${fillStyle(id)}" aria-hidden="true"></span>`;
  }
  function chartTitle(id) {
    const n = nodes[id];
    return n.kind === "crate"
      ? n.name
      : `${nodes["crate:" + n.crate].name} / ${n.name}`;
  }
  function hoverSummary(id) {
    const n = nodes[id],
      c = execution(n),
      coverage = state.enabled.some((id) =>
        measured.coverageGroups.includes(id),
      );
    if (mutationOnly())
      return `Mutations caught by tests: ${mutationStats(n).noticed}`;
    if (!state.enabled.length) return "No techniques selected";
    return coverage && !c.unmeasured
      ? `${Math.round((c.hit / Math.max(1, c.total)) * 100)}% of lines reached`
      : "Lines reached: —";
  }
  function techniqueStats(c, id) {
    const known = measured.coverageGroups.includes(id) && !c.unmeasured,
      hit = c.byKind[id] || 0,
      pct = known ? (hit / Math.max(1, c.total)) * 100 : 0;
    return {
      known,
      pct,
      label: known
        ? `${hit} of ${c.total} lines`
        : c.unmeasured
          ? "No compiler coverage mapping."
          : "No coverage data recorded.",
    };
  }
  function techniqueBar(id, value) {
    return `<span class="technique-track"><span class="technique-bar" style="width:${value.pct}%;${id ? fillStyle(id) : "background-color:var(--foreground)"}"></span></span><span class="tabular-nums">${value.known ? Math.round(value.pct) + "%" : "—"}</span>`;
  }
  function chartBody(id) {
    const n = nodes[id],
      c = execution(n);
    if (c.unmeasured)
      return `<div class="text-small">${esc(roleName(n))}</div><div class="text-small">No compiler coverage mapping for this module.</div>`;
    const rows = state.enabled
      .filter((id) => id !== "mutation")
      .map((id) => {
        const value = techniqueStats(c, id),
          m = mechanisms[id];
        return `<div class="technique-row" aria-label="${esc(m.name + ": " + value.label)}"><span>${esc(m.name)}</span>${techniqueBar(id, value)}</div>`;
      })
      .join("");
    return `<div class="text-small">${esc(roleName(n))}</div><div class="chart-bars text-small">${rows || (!state.enabled.length ? "<span>No techniques selected.</span>" : "")}</div>${state.enabled.includes("mutation") ? `<div class="text-small">${esc(mutationText(n))}</div>` : ""}<div class="text-small">${!state.enabled.some((id) => id !== "mutation" && measured.coverageGroups.includes(id)) ? "" : c.total ? `${c.hit.toLocaleString()} / ${c.total.toLocaleString()} lines reached (${Math.round((c.hit / c.total) * 100)}%)` : "No executable Rust lines measured."}</div>`;
  }
  function connectionSummary(id) {
    if (!state.enabled.length) return "No techniques selected.";
    if (mutationOnly()) return mutationText(nodes[id]);
    if (!state.enabled.some((id) => measured.coverageGroups.includes(id)))
      return "No coverage data for the selected techniques.";
    const c = execution(nodes[id]);
    return c.unmeasured
      ? "No compiler coverage mapping."
      : `${Math.round((c.hit / Math.max(1, c.total)) * 100)}% · ${c.hit.toLocaleString()}/${c.total.toLocaleString()} lines`;
  }
  function showConnection(edge) {
    const el = $("#ng-hover"),
      same = preview?.edge === edge.id,
      open = same && !!el.querySelector("[data-connection-details]")?.open,
      from = execution(nodes[edge.source]),
      to = execution(nodes[edge.target]),
      endpoint = (id, direction) =>
        `<button type="button" class="btn btn-ghost text-small" data-inspect-node="${esc(id)}" data-tooltip="Open this coverage chart">${direction}: ${esc(chartTitle(id))}</button>`,
      rows = state.enabled
        .filter((id) => id !== "mutation")
        .map((id) => {
          const a = techniqueStats(from, id),
            b = techniqueStats(to, id),
            m = mechanisms[id];
          return `<div class="technique-row" aria-label="${esc(m.name + ", from " + chartTitle(edge.source) + ": " + a.label + "; to " + chartTitle(edge.target) + ": " + b.label)}"><span>${esc(m.name)}</span>${techniqueBar(id, a)}${techniqueBar(id, b)}</div>`;
        })
        .join(""),
      available = state.enabled.some((id) =>
        measured.coverageGroups.includes(id),
      ),
      overall = (c) => ({
        known: available && !c.unmeasured,
        pct:
          available && !c.unmeasured ? (c.hit / Math.max(1, c.total)) * 100 : 0,
      }),
      mutations =
        state.enabled.includes("mutation") && !mutationOnly()
          ? `<div class="text-small">From: ${esc(mutationText(nodes[edge.source]))}</div><div class="text-small">To: ${esc(mutationText(nodes[edge.target]))}</div>`
          : "",
      totals = `<div class="comparison-totals text-small"><span>${mutationOnly() ? "Mutations" : "Lines"}</span><span>${esc(connectionSummary(edge.source))}</span><span>${esc(connectionSummary(edge.target))}</span></div>`,
      bars = mutationOnly()
        ? totals
        : `<div class="technique-row comparison-overall text-small" aria-label="Overall line coverage"><span>Overall</span>${techniqueBar(null, overall(from))}${techniqueBar(null, overall(to))}</div>`,
      imports = `<div class="text-small">${edge.weight} distinct ${edge.weight === 1 ? "import path" : "import paths"}</div>`,
      details = `<details data-connection-details${open ? " open" : ""}><summary>${mutationOnly() ? "Connection details" : "Compare techniques"}</summary>${mutationOnly() ? "" : `<div class="chart-bars text-small">${rows || "No techniques selected."}</div>${totals}${mutations}`}${imports}</details>`,
      html = `<div class="comparison-heading"><div class="inspection-title" data-chart-drag><span class="chart-name">${mutationOnly() ? "Mutation comparison" : "Coverage comparison"}</span><div class="chart-actions"><button type="button" class="btn btn-ghost" data-close-connection aria-label="Close connection" data-tooltip="Close connection"><i data-lucide="x" aria-hidden="true"></i></button></div></div><div class="comparison-head text-small"><span>${endpoint(edge.source, "From")}</span><span>${endpoint(edge.target, "To")}</span></div></div>${bars}${details}`;
    if (!same) {
      preview = { id: edge.target, edge: edge.id, x: 0, y: 0 };
      el.__html = null;
    }
    el.classList.add("connection");
    el.setAttribute("aria-label", "Import connection comparison");
    if (el.__html !== html) {
      el.innerHTML = html;
      el.__html = html;
      decorateIcons();
    }
    el.hidden = false;
    positionCards();
  }
  function hidePreview(force = false) {
    if (
      !force &&
      preview &&
      (preview.id === state.selected || cardDrag?.c === preview)
    )
      return;
    preview = null;
    $("#ng-hover").hidden = true;
    sizeCardSpace();
  }
  function cardRect(el) {
    return {
      x: parseFloat(el.style.left) || 0,
      y: parseFloat(el.style.top) || 0,
      w: el.offsetWidth,
      h: el.offsetHeight,
    };
  }
  function cardOverlap(a, b, gap = 10) {
    return (
      a.x < b.x + b.w + gap - 0.01 &&
      a.x + a.w + gap > b.x + 0.01 &&
      a.y < b.y + b.h + gap - 0.01 &&
      a.y + a.h + gap > b.y + 0.01
    );
  }
  function cardObstacles(except) {
    return [...$("#ng-inspectors").children]
      .filter((el) => el !== except)
      .map((el) => ({ ...cardRect(el), id: el.dataset.inspector }));
  }
  function cardSpaceHeight() {
    return height || 540;
  }
  // Open charts in a corner, against the graph's sides, by default. Do not anchor them
  // to the node or pointer. Charts must stay inside the fixed canvas, never enlarge it.
  // Only an explicit drag gives a chart a position away from the corners.
  function placeCard(c, el, placed) {
    const w = el.offsetWidth,
      h = el.offsetHeight,
      right = Math.max(8, width - w - 8),
      bottom = Math.max(8, cardSpaceHeight() - h - 8),
      node = c.corner === undefined ? screen[c.id] : null,
      candidates = [
        { x: right, y: 8 },
        { x: 8, y: 8 },
        { x: right, y: bottom },
        { x: 8, y: bottom },
      ].map(({ x, y }, corner) => ({
        x,
        y,
        corner,
        overlap: placed.reduce(
          (sum, other) =>
            sum +
            Math.max(
              0,
              Math.min(x + w, other.x + other.w) - Math.max(x, other.x),
            ) *
              Math.max(
                0,
                Math.min(y + h, other.y + other.h) - Math.max(y, other.y),
              ),
          node &&
            Math.hypot(
              node.x - Math.max(x, Math.min(x + w, node.x)),
              node.y - Math.max(y, Math.min(y + h, node.y)),
            ) <
              node.r + 4
            ? w * h
            : 0,
        ),
      })),
      { x, y, corner } = candidates.reduce((best, candidate) =>
        candidate.overlap < best.overlap ||
        (candidate.overlap === best.overlap && candidate.corner === c.corner)
          ? candidate
          : best,
      );
    c.corner = corner;
    c.x = x;
    c.y = y;
    el.style.left = x + "px";
    el.style.top = y + "px";
    return { x, y, w, h, manual: false };
  }
  function sizeCardSpace() {
    const minHeight = cardSpaceHeight() + "px";
    if ($(".board").style.minHeight !== minHeight)
      $(".board").style.minHeight = minHeight;
  }
  function decorateIcons() {
    if (root.querySelector("i[data-lucide]"))
      window.lucide?.createIcons({ attrs: { width: 16, height: 16 } });
  }
  function exactCard(c, el) {
    const w = el.offsetWidth,
      h = el.offsetHeight,
      x = Math.max(0, Math.min(Math.max(0, $(".board").clientWidth - w), c.x)),
      y = Math.max(0, Math.min(Math.max(0, cardSpaceHeight() - h), c.y));
    el.style.left = x + "px";
    el.style.top = y + "px";
    return { x, y, w, h, manual: !!c.manual };
  }
  function stickyAxis(axis, current, delta, p, others) {
    const d = cardDrag,
      other = axis === "x" ? "y" : "x",
      size = axis === "x" ? "w" : "h",
      otherSize = axis === "x" ? "h" : "w",
      direction = Math.sign(delta);
    if (!direction) return current;
    const held = d.holds[axis];
    if (held) {
      if (direction !== held.direction) {
        delete d.holds[axis];
        return current + delta;
      }
      held.pressure += Math.abs(delta);
      if (held.pressure <= 6) return held.position;
      d.passed.add(held.key);
      delete d.holds[axis];
      return held.position + direction * (held.pressure - 6);
    }
    const target = current + delta;
    let nearest = null;
    for (const o of others) {
      if (
        p[other] >= o[other] + o[otherSize] ||
        p[other] + p[otherSize] <= o[other]
      )
        continue;
      const position =
          direction > 0 ? o[axis] - p[size] - 10 : o[axis] + o[size] + 10,
        key = o.id + ":" + axis + ":" + direction;
      if (
        d.passed.has(key) ||
        direction * (position - current) < -0.01 ||
        direction * (target - position) < -4
      )
        continue;
      const distance = Math.abs(position - current);
      if (!nearest || distance < nearest.distance)
        nearest = { key, position, direction, distance };
    }
    if (!nearest) return target;
    const pressure = Math.max(0, direction * (target - nearest.position));
    if (pressure > 6) {
      d.passed.add(nearest.key);
      return target;
    }
    d.holds[axis] = { ...nearest, pressure };
    return nearest.position;
  }
  function dragCard(c, el, dx, dy) {
    const p = cardRect(el),
      others = cardObstacles(el);
    p.x = stickyAxis("x", p.x, dx, p, others);
    p.y = stickyAxis("y", p.y, dy, p, others);
    c.x = Math.max(
      0,
      Math.min(Math.max(0, $(".board").clientWidth - p.w), p.x),
    );
    c.y = Math.max(0, Math.min(Math.max(0, cardSpaceHeight() - p.h), p.y));
    c.manual = true;
    el.style.left = c.x + "px";
    el.style.top = c.y + "px";
  }
  function chartHeader(id, pinned = false) {
    const action = pinned ? "Unpin chart" : "Pin chart";
    return `<div class="inspection-title" data-chart-drag><span class="chart-name">${esc(chartTitle(id))}</span><div class="chart-actions"><button type="button" class="btn btn-ghost" data-pin-node="${esc(id)}" aria-pressed="${pinned}" aria-label="${action}" data-tooltip="${action}"><i data-lucide="${pinned ? "pin-off" : "pin"}" aria-hidden="true"></i></button><button type="button" class="btn btn-ghost" data-close-chart="${esc(id)}" aria-label="Close chart" data-tooltip="Close chart"><i data-lucide="x" aria-hidden="true"></i></button></div></div>`;
  }
  function showPreview(id) {
    if (id !== state.selected) return;
    if (inspectors.some((c) => c.id === id)) {
      hidePreview(true);
      return;
    }
    const el = $("#ng-hover"),
      p = screen[id];
    if (!p) return;
    const same = preview?.id === id && !preview.edge;
    if (!same) preview = { id, x: 0, y: 0 };
    el.classList.remove("connection");
    el.setAttribute("aria-label", "Coverage preview");
    const html = chartHeader(id) + chartBody(id);
    if (el.__html !== html) {
      el.innerHTML = html;
      el.__html = html;
      decorateIcons();
    }
    el.hidden = false;
    positionCards();
    sizeCardSpace();
  }
  function pinInspector(id, save = true, pinned = true) {
    if (!nodes[id]) return;
    let c = inspectors.find((c) => c.id === id);
    if (c) {
      if (pinned) c.pinned = true;
    } else {
      const fromPreview = preview?.id === id;
      c = {
        id,
        x: fromPreview ? preview.x : 0,
        y: fromPreview ? preview.y : 0,
        manual: fromPreview && !!preview.manual,
        corner: fromPreview ? preview.corner : undefined,
        pinned,
      };
      inspectors.push(c);
    }
    if (save) {
      render();
      persist();
    }
  }
  function togglePin(id) {
    const c = inspectors.find((c) => c.id === id);
    if (!c) {
      pinInspector(id);
      return;
    }
    c.pinned = !c.pinned;
    if (!c.pinned && !state.selectedNodes.includes(id))
      inspectors = inspectors.filter((c) => c.id !== id);
    render();
    persist();
  }
  function closeChart(id) {
    inspectors = inspectors.filter((c) => c.id !== id);
    if (preview?.id === id && !preview.edge) hidePreview(true);
    if (state.selectedNodes.includes(id) && !state.selectedEdge) {
      state.selectedNodes = state.selectedNodes.filter((x) => x !== id);
      state.selected = state.selectedNodes.includes(state.selected)
        ? state.selected
        : state.selectedNodes.at(-1) || null;
      state.selectedEdge = null;
      edgeId = null;
      if (state.focus === id) state.focus = null;
      hover = null;
      tip.hidden = true;
    }
    render();
    persist();
  }

  function positionCards() {
    const cards = inspectors.flatMap((c) => {
        const el = [...$("#ng-inspectors").children].find(
          (el) => el.dataset.inspector === c.id,
        );
        return el ? [{ c, el }] : [];
      }),
      placed = cards
        .filter(({ c }) => c.manual)
        .map(({ c, el }) => exactCard(c, el)),
      el = $("#ng-hover");
    if (preview?.manual && !el.hidden) placed.push(exactCard(preview, el));
    for (const { c, el } of cards)
      if (!c.manual) placed.push(placeCard(c, el, placed));
    if (preview && !preview.manual && !el.hidden)
      placeCard(preview, el, placed);
  }
  function renderInspectors() {
    inspectors = inspectors.filter(
      (c) =>
        c.pinned || (!state.selectedEdge && state.selectedNodes.includes(c.id)),
    );
    const area = $("#ng-inspectors");
    for (const el of [...area.children])
      if (!inspectors.some((c) => c.id === el.dataset.inspector)) el.remove();
    for (const c of inspectors) {
      let el = [...area.children].find((el) => el.dataset.inspector === c.id);
      if (!el) {
        el = document.createElement("div");
        el.className = "card inspection";
        el.dataset.inspector = c.id;
        el.setAttribute("role", "group");
        el.setAttribute("aria-label", chartTitle(c.id) + " coverage");
        area.append(el);
      }
      const html = chartHeader(c.id, c.pinned) + chartBody(c.id);
      if (el.__html !== html) {
        el.innerHTML = html;
        el.__html = html;
        decorateIcons();
      }
    }
    const edge = state.selectedEdge
      ? view.links.find((e) => e.id === state.selectedEdge)
      : null;
    if (edge) showConnection(edge);
    else {
      if (
        preview &&
        (inspectors.some((c) => c.id === preview.id) ||
          (state.selected && preview.id !== state.selected))
      )
        hidePreview(true);
      if (state.selected && !inspectors.some((c) => c.id === state.selected))
        showPreview(state.selected);
      else if (preview) hidePreview(true);
    }
    sizeCardSpace();
    positionCards();
  }
  root.addEventListener("pointerdown", (e) => {
    if (!e.target.closest("[data-chart-drag]") || e.target.closest("button"))
      return;
    const el = e.target.closest(".inspection"),
      c =
        el.id === "ng-hover"
          ? preview
          : inspectors.find((c) => c.id === el.dataset.inspector);
    if (!c) return;
    e.preventDefault();
    if (el.id !== "ng-hover") el.parentElement.append(el);
    const r = cardRect(el);
    c.x = r.x;
    c.y = r.y;
    c.manual = true;
    cardDrag = {
      c,
      el,
      x: e.clientX,
      y: e.clientY,
      holds: {},
      passed: new Set(),
    };
    root.setPointerCapture(e.pointerId);
  });
  root.addEventListener("pointermove", (e) => {
    if (!cardDrag) return;
    const d = cardDrag,
      dx = e.clientX - d.x,
      dy = e.clientY - d.y;
    d.x = e.clientX;
    d.y = e.clientY;
    dragCard(d.c, d.el, dx, dy);
  });
  $("#ng-hover").addEventListener("pointerleave", () => hidePreview());
  root.addEventListener("pointerleave", () => hidePreview());
  function endCardDrag(e) {
    if (!cardDrag) return;
    cardDrag = null;
    if (root.hasPointerCapture(e.pointerId))
      root.releasePointerCapture(e.pointerId);
    persist();
  }
  root.addEventListener("pointerup", endCardDrag);
  root.addEventListener("pointercancel", endCardDrag);

  function renderControls() {
    const cutoff = events.reduce(
        (n, e, i) => (e.t <= state.time ? i + 1 : n),
        0,
      ),
      selection = state.enabled.join("|"),
      key = selection + "@" + cutoff;
    if (key !== coverageKey) {
      coverageCache.clear();
      coverageKey = key;
    }
    if (selection !== scopeKey) {
      scopeCache.clear();
      scopeKey = selection;
    }
    renderInteraction();
    for (const m of data.mechanisms)
      root.querySelector(`[data-mechanism="${m.id}"]`).checked =
        state.enabled.includes(m.id);
    for (const c of components)
      root.querySelector(`[data-expand-component="${c.crate}"]`).checked =
        state.expanded.includes(c.crate);
    $("#ng-technique-count").textContent =
      `${state.enabled.length}/${data.mechanisms.length}`;
    $("#ng-techniques-all").disabled =
      state.enabled.length === data.mechanisms.length;
    $("#ng-techniques-none").disabled = state.enabled.length === 0;
    const allExpanded = state.expanded.length === components.length;
    $("#ng-toggle-all").textContent = allExpanded
      ? "Collapse all"
      : "Expand all";
    $("#ng-node").innerHTML =
      '<option value="">No selection</option>' +
      view.nodes
        .slice()
        .sort((a, b) => nodes[a].label.localeCompare(nodes[b].label))
        .map(
          (id) =>
            `<option value="${esc(id)}">${esc(nodes[id].kind === "crate" ? nodes[id].name : nodes[id].label)}</option>`,
        )
        .join("");
    $("#ng-node").value = state.selected || "";
    const owner =
      nodes["crate:" + (nodes[state.selected]?.crate || state.component)];
    $("#ng-toggle-component").textContent =
      `${state.expanded.includes(owner.crate) ? "Collapse" : "Expand"} ${owner.name}`;
    const c = view.nodes.filter((id) => nodes[id].kind === "crate").length,
      m = view.nodes.length - c;
    $("#ng-counts").textContent = [
      c ? `${c} crates` : null,
      m ? `${m} modules` : null,
    ]
      .filter(Boolean)
      .join(" · ");
    const all = Object.keys(measured.files).map(fileCoverage),
      hit = all.reduce((s, c) => s + c.hit, 0),
      total = all.reduce((s, c) => s + c.total, 0),
      available = state.enabled.some((id) =>
        measured.coverageGroups.includes(id),
      );
    $("#ng-summary").textContent = !state.enabled.length
      ? "No techniques selected."
      : available
        ? `${hit.toLocaleString()} of ${total.toLocaleString()} executable Rust lines reached (${Math.round((hit / total) * 100)}%).`
        : "No coverage data for the selected techniques.";
    if (mutationOnly()) $("#ng-summary").textContent = mutationText();
    $("#ng-clock").value = state.clock;
    $("#ng-time").max = state.clock === "effort" ? measured.effort : duration;
    $("#ng-time").value =
      state.clock === "effort" ? effort(state.time) : state.time;
    const done = events.filter((e) => e.t <= state.time).length;
    $("#ng-time-label").textContent =
      `${formatTime(state.clock === "effort" ? effort(state.time) : state.time)} · ${done}/${events.length} completed`;
    const replayReason = available
      ? ""
      : !state.enabled.length
        ? "No techniques selected. Open Techniques and select All or a test or fuzzing technique."
        : mutationOnly()
          ? "Mutation results have no replay timeline. Select a test or fuzzing technique under Techniques."
          : "No timeline recorded for the selected techniques. Choose another technique under Techniques.";
    for (const id of ["#ng-replay-help", "#ng-time-help"])
      if (replayReason) $(id).dataset.tooltip = replayReason;
      else $(id).removeAttribute("data-tooltip");
    $("#ng-replay-description").textContent = replayReason;
    if (replayReason) $("#ng-replay-help").setAttribute("tabindex", "0");
    else $("#ng-replay-help").removeAttribute("tabindex");
    $("#ng-clock-help").dataset.tooltip =
      state.clock === "effort"
        ? "Adds each test and fuzz run's duration, including overlapping runs. Two parallel 10-second runs add 20 seconds."
        : "Time along the recorded test and fuzz runs; concurrent tests overlap. Two parallel 10-second tests take 10 seconds on this clock. Separate captures are joined consecutively.";
    if (!available && playing) stop();
    $("#ng-play").textContent = playing ? "Pause" : "Replay";
    $("#ng-play").disabled = !available;
    $("#ng-time").disabled = !available;
    $("#ng-run-counts").textContent =
      `${measured.passed} tests · ${measured.fuzzCheckpoints || 0} fuzz checkpoints`;
    const source = $("#ng-source");
    source.textContent = measured.sourceRevision.slice(0, 8);
    source.href = `https://github.com/bos/jj-musubi/tree/${encodeURIComponent(measured.sourceRevision)}`;
    source.setAttribute(
      "aria-label",
      `Browse source at commit ${measured.sourceRevision}`,
    );
  }

  function renderDetail() {
    const pinned = inspectors.some((c) => c.id === state.selected && c.pinned),
      pin = $("#ng-pin"),
      action = pinned ? "Unpin chart" : "Pin chart";
    pin.setAttribute("aria-pressed", String(pinned));
    pin.setAttribute("aria-label", action);
    pin.dataset.tooltip = action;
    if (pin.dataset.pinned !== String(pinned)) {
      pin.dataset.pinned = String(pinned);
      pin.innerHTML = `<i data-lucide="${pinned ? "pin-off" : "pin"}" aria-hidden="true"></i>`;
      decorateIcons();
    }
    const n = nodes[state.selected],
      edge = edgeId ? view.links.find((e) => e.id === edgeId) : null;
    $(".selection").hidden = !n && !edge;
    $(".actions").hidden = !n || !!edge;
    $("#ng-toggle-component").hidden = !n || !!edge;
    $("#ng-center").hidden = !n || !!edge;
    $("#ng-pin").hidden = !n || !!edge;
    if (edge) {
      $("#ng-name").textContent =
        `${nodes[edge.source].name} → ${nodes[edge.target].name}`;
      $("#ng-related").textContent = `${edge.weight} distinct import paths.`;
      $("#ng-execution-detail").textContent = "";
      return;
    }
    if (!n) {
      $("#ng-name").textContent = "";
      $("#ng-related").textContent = "";
      $("#ng-execution-detail").textContent = "";
      return;
    }
    $("#ng-name").textContent =
      n.kind === "crate"
        ? n.name
        : `${nodes["crate:" + n.crate].name} / ${n.name}`;
    const related = nodeKinds(n).map((id) => mechanisms[id].name);
    $("#ng-related").textContent = related.length
      ? related.join(" · ")
      : "No proof/test categories for this selection.";
    const c = execution(n),
      available = state.enabled.some((id) =>
        measured.coverageGroups.includes(id),
      );
    $("#ng-execution-detail").textContent = !available
      ? !state.enabled.length
        ? "No techniques selected."
        : "No coverage data for the selected techniques."
      : c.unmeasured
        ? "No compiler coverage mapping for this module."
        : `${c.hit.toLocaleString()} of ${c.total.toLocaleString()} executable Rust lines reached (${Math.round((c.hit / Math.max(1, c.total)) * 100)}%).`;
    if (mutationOnly()) $("#ng-execution-detail").textContent = mutationText(n);
  }

  function render() {
    renderControls();
    renderDetail();
    draw();
    renderInspectors();
  }
  function clearSelection() {
    cancelAnimationFrame(cameraFrame);
    state.selected = null;
    state.selectedNodes = [];
    state.selectedEdge = null;
    state.focus = null;
    hover = null;
    edgeId = null;
    sourceId = null;
    tip.hidden = true;
    hidePreview();
    render();
    persist();
  }
  function selectNode(id, add = false) {
    if (!id) {
      clearSelection();
      return;
    }
    if (!nodes[id]) return;
    if (add) {
      if (state.selectedNodes.includes(id)) {
        state.selectedNodes = state.selectedNodes.filter((x) => x !== id);
        inspectors = inspectors.filter((c) => c.id !== id || c.pinned);
      } else state.selectedNodes.push(id);
      state.selected = state.selectedNodes.includes(id)
        ? id
        : state.selectedNodes.at(-1) || null;
      state.selectedNodes.forEach((id) => pinInspector(id, false, false));
    } else {
      state.selected = id;
      state.selectedNodes = [id];
    }
    state.component = nodes[id].crate;
    if (state.focus !== state.selected) state.focus = null;
    edgeId = null;
    state.selectedEdge = null;
    sourceId = null;
    hover = null;
    tip.hidden = true;
    render();
    persist();
  }
  function selectEdge(id) {
    const e = view.links.find((e) => e.id === id);
    if (!e) return;
    cancelAnimationFrame(cameraFrame);
    state.selectedNodes = [e.source, e.target];
    state.selected = e.target;
    state.component = nodes[e.target].crate;
    state.focus = null;
    state.selectedEdge = id;
    edgeId = id;
    hover = null;
    sourceId = null;
    tip.hidden = true;
    hidePreview(true);
    inspectors = inspectors.filter((c) => c.pinned);
    render();
    persist();
  }
  function setExpanded(name, on) {
    if (!componentNames.includes(name)) return;
    state.expanded = componentNames.filter((c) =>
      c === name ? on : state.expanded.includes(c),
    );
    state.level = expansionLevel();
    setView({ resetCamera: false });
    render();
    persist();
  }
  function expand(name) {
    setExpanded(name, true);
  }
  function clockMap(t, from, to) {
    let previous = { [from]: 0, [to]: 0 };
    for (const next of events) {
      if (next[from] >= t) {
        const f =
          (t - previous[from]) /
          Math.max(0.000001, next[from] - previous[from]);
        return previous[to] + f * (next[to] - previous[to]);
      }
      previous = next;
    }
    return previous[to];
  }
  function effort(t) {
    return clockMap(t, "t", "e");
  }
  function fromEffort(t) {
    return clockMap(t, "e", "t");
  }
  function formatTime(t) {
    const s = Math.round(t);
    return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, "0")}`;
  }
  function stop() {
    playing = false;
    cancelAnimationFrame(playFrame);
    lastTick = 0;
  }

  function tick(t) {
    if (!playing) return;
    const total = state.clock === "effort" ? measured.effort : duration;
    if (!lastTick || replayClock !== state.clock) {
      replayClock = state.clock;
      replayPosition =
        state.clock === "effort" ? effort(state.time) : state.time;
    } else {
      replayPosition = Math.min(
        total,
        replayPosition + ((t - lastTick) / 1000) * (total / 8),
      );
    }
    lastTick = t;
    state.time =
      replayPosition >= total
        ? duration
        : state.clock === "effort"
          ? fromEffort(replayPosition)
          : replayPosition;
    render();
    if (replayPosition >= total) {
      stop();
      renderControls();
      persist();
    } else playFrame = requestAnimationFrame(tick);
  }

  $("#ng-roles").innerHTML =
    "<span>Rims &amp; arrows:</span>" +
    data.roles
      .map(
        (r) =>
          `<span class="role-item"><span class="role-key" data-role="${r.id}" style="background:${r.series ? `var(--viz-series-${r.series})` : "var(--muted-foreground)"}" aria-hidden="true"></span>${esc(r.name)}</span>`,
      )
      .join("");
  $("#ng-expansions").innerHTML = components
    .map(
      (c) =>
        `<label class="form-check"><input class="form-check-input" type="checkbox" data-expand-component="${esc(c.crate)}"><span class="form-check-label">${esc(c.name)}</span></label>`,
    )
    .join("");
  $("#ng-mechanisms").innerHTML = data.mechanisms
    .map(
      (m) =>
        `<div class="method" data-tooltip="${esc(m.description)} ${m.tests} ${m.id === "fuzz" ? "coverage checkpoints" : m.id === "mutation" ? "mutations" : "recorded tests"}.">${swatch(m.id)}<label class="form-check"><input class="form-check-input" type="checkbox" data-mechanism="${m.id}" checked><span class="form-check-label">${esc(m.name)}</span></label>${m.status !== "recorded" ? '<span class="text-small text-muted">no data</span>' : ""}</div>`,
    )
    .join("");
  root.addEventListener("pointerdown", (e) => {
    for (const id of ["ng-techniques", "ng-legend", "ng-explore"]) {
      const panel = document.getElementById(id);
      if (panel.open && !panel.contains(e.target)) panel.open = false;
    }
  });
  for (const id of ["ng-techniques", "ng-legend", "ng-explore"]) {
    const panel = document.getElementById(id);
    panel.addEventListener("toggle", () => {
      if (panel.open)
        for (const other of ["ng-techniques", "ng-legend", "ng-explore"])
          if (other !== id) document.getElementById(other).open = false;
    });
    panel.addEventListener("keydown", (e) => {
      if (e.key === "Escape") {
        panel.open = false;
        panel.querySelector("summary").focus();
      }
    });
  }
  root.addEventListener("change", (e) => {
    const t = e.target;
    if (t.dataset.expandComponent) {
      setExpanded(t.dataset.expandComponent, t.checked);
      return;
    }
    if (t.id === "ng-node") {
      selectNode(t.value);
      return;
    }
    if (t.dataset.mechanism) {
      const id = t.dataset.mechanism;
      state.enabled = data.mechanisms
        .map((m) => m.id)
        .filter((m) => (m === id ? t.checked : state.enabled.includes(m)));
    } else if (t.id === "ng-clock") state.clock = t.value;
    else return;
    render();
    persist();
  });
  root.addEventListener(
    "toggle",
    (e) => {
      if (e.target.matches("[data-connection-details]")) positionCards();
    },
    true,
  );
  root.addEventListener("click", (e) => {
    if (e.target.closest("[data-close-connection]")) {
      clearSelection();
      return;
    }
    const endpoint = e.target.closest("[data-inspect-node]");
    if (endpoint) {
      selectNode(endpoint.dataset.inspectNode);
      return;
    }

    const techniques = e.target.closest(
      "#ng-techniques-all, #ng-techniques-none",
    );
    if (techniques) {
      state.enabled =
        techniques.id === "ng-techniques-all"
          ? data.mechanisms.map((m) => m.id)
          : [];
      render();
      persist();
      return;
    }
    const pin = e.target.closest("[data-pin-node]"),
      close = e.target.closest("[data-close-chart]");
    if (pin) {
      togglePin(pin.dataset.pinNode);
      return;
    }
    if (close) {
      closeChart(close.dataset.closeChart);
      return;
    }
    if (e.target.closest("[data-hide-preview]")) {
      if (preview?.id === state.selected) clearSelection();
      else hidePreview(true);
      return;
    }
    if (e.target.closest("#ng-pin")) {
      togglePin(state.selected);
      return;
    }
    if (e.target.closest("#ng-toggle-component")) {
      const name = nodes[state.selected].crate;
      setExpanded(name, !state.expanded.includes(name));
      return;
    }
    if (e.target.closest("#ng-center")) {
      centerConnections(state.selected);
      return;
    }
    if (e.target.closest("#ng-whole")) {
      wholeNetwork();
      return;
    }
    const geometry = e.target.closest("#ng-toggle-all");
    if (geometry) {
      state.expanded =
        state.expanded.length === componentNames.length
          ? []
          : [...componentNames];
      state.level = expansionLevel();
      state.focus = null;
      setView();
      render();
      persist();
      return;
    }
    if (e.target.closest("#ng-play")) {
      if (playing) {
        stop();
        renderControls();
        persist();
        return;
      }
      if (state.time >= duration) state.time = 0;
      playing = true;
      lastTick = 0;
      render();
      playFrame = requestAnimationFrame(tick);
      persist();
    }
  });
  $("#ng-time").addEventListener("input", (e) => {
    stop();
    state.time =
      state.clock === "effort"
        ? fromEffort(Number(e.target.value))
        : Number(e.target.value);
    render();
  });
  $("#ng-time").addEventListener("change", persist);
  function groupAt(x, y) {
    return groupHits
      .slice()
      .reverse()
      .find((g) =>
        g.poly.every((a, i) => {
          const b = g.poly[(i + 1) % g.poly.length],
            dx = b.x - a.x,
            dy = b.y - a.y;
          return dx * (y - a.y) - dy * (x - a.x) >= -3 * Math.hypot(dx, dy);
        }),
      );
  }
  function hit(x, y, precise = false) {
    if (x > graphWidth()) return null;
    const nearby = hits
        .filter((h) => h.type === "node" && Math.hypot(h.x - x, h.y - y) < h.r)
        .sort(
          (a, b) => Math.hypot(a.x - x, a.y - y) - Math.hypot(b.x - x, b.y - y),
        ),
      circle = nearby.find(
        (h) => Math.hypot(h.x - x, h.y - y) <= screen[h.id].r,
      );
    if (circle) return circle;
    if (!precise) {
      const label = hits.find(
        (h) =>
          h.type === "label" &&
          x >= h.x &&
          x <= h.x + h.w &&
          y >= h.y &&
          y <= h.y + h.h,
      );
      if (label) return { ...label, type: "node" };
      if (nearby.length) return nearby[0];
    }
    let best = null,
      distance = 8;
    for (const h of hits)
      if (h.type === "edge") {
        const dx = h.b.x - h.a.x,
          dy = h.b.y - h.a.y,
          t = Math.max(
            0,
            Math.min(
              1,
              ((x - h.a.x) * dx + (y - h.a.y) * dy) / (dx * dx + dy * dy || 1),
            ),
          ),
          d = Math.hypot(x - h.a.x - t * dx, y - h.a.y - t * dy);
        if (d < distance) {
          distance = d;
          best = h;
        }
      }
    return best || groupAt(x, y);
  }
  function local(e) {
    const b = canvas.getBoundingClientRect();
    return { x: e.clientX - b.left, y: e.clientY - b.top };
  }
  function directCamera() {
    cancelAnimationFrame(cameraFrame);
    hover = null;
    tip.hidden = true;
    hidePreview();
  }
  function zoomAt(p, scale) {
    const old = cam.scale;
    cam.scale = Math.max(0.25, Math.min(8, scale));
    if (state.focus) state.focusScale = cam.scale;
    const ratio = cam.scale / old;
    cam.x = p.x - graphWidth() / 2 - (p.x - graphWidth() / 2 - cam.x) * ratio;
    cam.y = p.y - height / 2 - (p.y - height / 2 - cam.y) * ratio;
  }
  function gesturePoint(e) {
    return Number.isFinite(e.clientX) && Number.isFinite(e.clientY)
      ? local(e)
      : { x: graphWidth() / 2, y: height / 2 };
  }
  function renderHoverTooltip() {
    const h = hover;
    if (!h || h.type === "group" || !tooltipPoint || drag?.moved) {
      tip.hidden = true;
      return;
    }
    if (h.type === "node") {
      tip.textContent = `${chartTitle(h.id)}\n${hoverSummary(h.id)}`;
    } else {
      const edge = view.links.find((e) => e.id === h.id);
      tip.textContent = `${chartTitle(edge.source)} · ${hoverSummary(edge.source)}\n${chartTitle(edge.target)} · ${hoverSummary(edge.target)}`;
    }
    tip.hidden = false;
    const box = root.getBoundingClientRect(),
      board = $(".board").getBoundingClientRect(),
      left = board.left - box.left,
      top = board.top - box.top,
      x = tooltipPoint.x - box.left + 12,
      y = tooltipPoint.y - box.top + 15,
      below = y + tip.offsetHeight <= top + height - 8;
    tip.style.left =
      Math.max(left + 8, Math.min(left + width - tip.offsetWidth - 8, x)) +
      "px";
    tip.style.top =
      Math.max(
        top + 8,
        Math.min(
          top + height - tip.offsetHeight - 8,
          below ? y : tooltipPoint.y - box.top - tip.offsetHeight - 12,
        ),
      ) + "px";
  }
  canvas.addEventListener("pointerdown", (e) => {
    cancelAnimationFrame(cameraFrame);
    const p = local(e);
    drag = {
      x: p.x,
      y: p.y,
      baseX: cam.x,
      baseY: cam.y,
      lastX: p.x,
      lastY: p.y,
      moved: false,
    };
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener("pointermove", (e) => {
    const p = local(e);
    if (drag) {
      drag.lastX = p.x;
      drag.lastY = p.y;
      const dx = p.x - drag.x,
        dy = p.y - drag.y;
      if (Math.hypot(dx, dy) > 4) drag.moved = true;
      if (drag.moved) {
        cam.x = drag.baseX + dx;
        cam.y = drag.baseY + dy;
        hover = null;
        tooltipPoint = null;
        tip.hidden = true;
        draw();
      }
      return;
    }
    const h = hit(p.x, p.y, true);
    hover = h;
    tooltipPoint =
      e.pointerType === "touch" ? null : { x: e.clientX, y: e.clientY };
    draw();
  });
  canvas.addEventListener("pointerup", (e) => {
    if (!drag) return;
    const moved = drag.moved;
    drag = null;
    if (canvas.hasPointerCapture(e.pointerId))
      canvas.releasePointerCapture(e.pointerId);
    if (!moved) {
      const p = local(e),
        // Keep a line click consistent with its tooltip where a label overlaps it.
        h = hit(p.x, p.y, hover?.type === "edge");
      if (h?.type === "node") selectNode(h.id, e.shiftKey);
      else if (h?.type === "edge") selectEdge(h.id);
      else clearSelection();
    }
  });
  canvas.addEventListener("pointercancel", () => {
    drag = null;
  });
  canvas.addEventListener("pointerleave", (e) => {
    if (!drag) {
      hover = null;
      tip.hidden = true;
      if (!e.relatedTarget?.closest?.("#ng-hover")) hidePreview();
      draw();
    }
  });
  canvas.addEventListener("dblclick", (e) => {
    e.preventDefault();
    if (e.shiftKey) return;
    const p = local(e),
      h = hit(p.x, p.y);
    if (h?.type === "node") doubleClickNode(h.id);
    else if (h?.type === "edge") return;
    else {
      const group = groupAt(p.x, p.y);
      if (group) setExpanded(group.crate, false);
    }
  });
  canvas.addEventListener(
    "wheel",
    (e) => {
      e.preventDefault();
      if (gesture) return;
      directCamera();
      const unit = e.deltaMode === 1 ? 16 : 1,
        dx = e.deltaX * unit * (e.deltaMode === 2 ? width : 1),
        dy = e.deltaY * unit * (e.deltaMode === 2 ? height : 1);
      if (e.ctrlKey) zoomAt(local(e), cam.scale * Math.exp(-dy * 0.01));
      else {
        cam.x -= dx;
        cam.y -= dy;
      }
      scheduleDraw();
    },
    { passive: false },
  );
  canvas.addEventListener(
    "gesturestart",
    (e) => {
      e.preventDefault();
      directCamera();
      gesture = { scale: cam.scale };
    },
    { passive: false },
  );
  canvas.addEventListener(
    "gesturechange",
    (e) => {
      e.preventDefault();
      if (!gesture || !Number.isFinite(e.scale) || e.scale <= 0) return;
      zoomAt(gesturePoint(e), gesture.scale * e.scale);
      scheduleDraw();
    },
    { passive: false },
  );
  canvas.addEventListener(
    "gestureend",
    (e) => {
      e.preventDefault();
      if (gesture && Number.isFinite(e.scale) && e.scale > 0) {
        zoomAt(gesturePoint(e), gesture.scale * e.scale);
        scheduleDraw();
      }
      gesture = null;
    },
    { passive: false },
  );
  const layoutObserver = new ResizeObserver(scheduleResize);
  layoutObserver.observe($(".board"));
  layoutObserver.observe(root);
  window.addEventListener("resize", scheduleResize);
  new MutationObserver(scheduleTheme).observe(document.documentElement, {
    attributes: true,
    attributeFilter: ["style", "class", "data-theme", "data-color-scheme"],
  });
  window
    .matchMedia("(prefers-color-scheme: dark)")
    .addEventListener("change", scheduleTheme);
  document.addEventListener("visibilitychange", () => {
    if (document.hidden && playing) {
      stop();
      renderControls();
      persist();
    }
  });
  setView();
  render();
  resize();
})();
