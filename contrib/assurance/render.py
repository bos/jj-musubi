"""Render a saved dataset without rebuilding the source tree or requiring the chat host."""

import json
from pathlib import Path

from common import HERE


def render(dataset, output, standalone=False):
    data = json.loads(Path(dataset).read_text())
    # Detailed provenance and test identities stay in the dataset, not in the figure payload.
    inline = {
        "roles": data["roles"],
        "nodeRoles": data["nodeRoles"],
        "mechanisms": data["mechanisms"],
        "claims": [{k: c[k] for k in ("id", "evidence")} for c in data["claims"]],
        "evidence": [{k: e[k] for k in ("id", "mechanism")} for e in data["evidence"]],
        "network": {
            k: data["network"][k]
            for k in ("nodes", "imports", "views", "measurement", "assurance")
        },
        "measured": {
            k: data["measured"][k]
            for k in (
                "sourceRevision",
                "sourceDigest",
                "duration",
                "effort",
                "captureId",
                "fuzzCheckpoints",
                "fuzzInputs",
                "coverageGroups",
                "passed",
                "failed",
                "events",
                "files",
                "mutation",
            )
        },
    }
    for event in inline["measured"]["events"]:
        for key in ("n", "m", "models", "ok", "inputs", "corpusFiles"):
            event.pop(key, None)
    for file in inline["measured"]["files"].values():
        file.pop("hash", None)
    inline["network"]["nodes"] = {
        id: {
            k: v
            for k, v in n.items()
            if k in ("id", "kind", "crate", "name", "label", "lines", "files", "claims")
        }
        for id, n in inline["network"]["nodes"].items()
    }
    inline["network"]["imports"] = [
        {k: e[k] for k in ("id", "source", "target")}
        for e in inline["network"]["imports"]
    ]
    fragment = (
        (HERE / "network.html.in")
        .read_text()
        .replace(
            "<!-- NETWORK_DATA -->",
            json.dumps(inline, sort_keys=True, separators=(",", ":")).replace(
                "</", "<\\/"
            ),
        )
    )
    fragment = fragment.replace(
        "<!-- NETWORK_LOGIC -->",
        (HERE / "network-view.js").read_text().replace("</", "<\\/"),
    )
    if len(fragment.encode()) >= 1_000_000:
        raise ValueError("Figure exceeds 1 MB; reduce payload before rendering")
    if "<!-- NETWORK_" in fragment:
        raise ValueError("Unfilled template marker")
    if standalone:
        icons = {
            name: (HERE / "icons" / (name + ".svg")).read_text()
            for name in ("pin", "pin-off", "x")
        }
        bootstrap = """window.lucide={createIcons(){for(const el of document.querySelectorAll('i[data-lucide]')){const text=ICONS[el.dataset.lucide];if(!text)continue;const svg=new DOMParser().parseFromString(text,'image/svg+xml').documentElement;svg.setAttribute('width','16');svg.setAttribute('height','16');svg.setAttribute('aria-hidden','true');el.replaceWith(document.importNode(svg,true));}}};
window.openai={widgetState:null,setWidgetState:async()=>{}};
""".replace("ICONS", json.dumps(icons))
        fragment = (
            '<!doctype html><html><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            "<title>Musubi assurance</title><style>"
            + (HERE / "standalone.css").read_text()
            + "</style><script>"
            + bootstrap
            + "</script></head><body>"
            + fragment
            + "<script>lucide.createIcons()</script></body></html>"
        )
    Path(output).parent.mkdir(parents=True, exist_ok=True)
    Path(output).write_text(fragment)
