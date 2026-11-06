// Offline pages use the same data-tooltip attributes as the embedded view.
(() => {
  const root = document.getElementById("musubi-code-network");
  const tooltip = document.createElement("div");
  tooltip.id = "ng-offline-tooltip";
  tooltip.className = "tooltip text-small";
  tooltip.setAttribute("role", "tooltip");
  tooltip.hidden = true;
  root.append(tooltip);
  let trigger = null;
  let describedElement = null;
  let originalDescription = null;

  function clearDescription() {
    if (!describedElement) return;
    if (originalDescription === null)
      describedElement.removeAttribute("aria-describedby");
    else describedElement.setAttribute("aria-describedby", originalDescription);
    describedElement = null;
  }

  const target = (element) =>
    element instanceof Element ? element.closest("[data-tooltip]") : null;
  function hide() {
    tooltip.hidden = true;
    trigger = null;
    clearDescription();
  }
  function show(element) {
    if (!element || !root.contains(element) || !element.dataset.tooltip) {
      hide();
      return;
    }
    trigger = element;
    const described = element.contains(document.activeElement)
      ? document.activeElement
      : element;
    if (described !== describedElement) {
      clearDescription();
      describedElement = described;
      originalDescription = described.getAttribute("aria-describedby");
      described.setAttribute(
        "aria-describedby",
        [originalDescription, tooltip.id].filter(Boolean).join(" "),
      );
    }
    tooltip.textContent = element.dataset.tooltip;
    tooltip.hidden = false;
    const bounds = root.getBoundingClientRect();
    const anchor = element.getBoundingClientRect();
    tooltip.style.maxWidth = `${Math.max(0, Math.min(300, bounds.width - 16))}px`;
    const x = Math.max(
      bounds.left + 8,
      Math.min(anchor.left, bounds.right - tooltip.offsetWidth - 8),
    );
    const below = anchor.bottom + 8;
    const y =
      below + tooltip.offsetHeight <= window.innerHeight
        ? below
        : Math.max(8, anchor.top - tooltip.offsetHeight - 8);
    tooltip.style.left = `${x - bounds.left}px`;
    tooltip.style.top = `${y - bounds.top}px`;
  }

  root.addEventListener("pointerover", (event) => show(target(event.target)));
  root.addEventListener("pointerout", (event) => {
    if (
      event.relatedTarget instanceof Node &&
      trigger?.contains(event.relatedTarget)
    )
      return;
    if (target(document.activeElement) === trigger) return;
    hide();
  });
  root.addEventListener("focusin", (event) => show(target(event.target)));
  root.addEventListener("focusout", (event) =>
    show(target(event.relatedTarget)),
  );
  root.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hide();
  });
  root.addEventListener("change", () => {
    if (trigger) show(trigger);
  });
  function viewportChanged() {
    if (trigger && target(document.activeElement) === trigger) show(trigger);
    else hide();
  }
  window.addEventListener("resize", viewportChanged);
  window.addEventListener("scroll", viewportChanged, true);
})();
