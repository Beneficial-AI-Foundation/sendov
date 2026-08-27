#!/usr/bin/env python3
"""Post-process the generated Verso blueprint site so every external Lean
declaration box carries a collapsible "Show Lean source" section containing
the full declaration (statement *and* proof) from the source file.

Verso only renders the declaration signature for `(lean := ...)` references.
This script uses the ranges recorded in `-verso-data/blueprint-manifest.json`
to slice the source files and inject a `<details>` block into every
`<div class="declaration decl ..." data-decl="...">` element, both in the
static pages and in the hover-preview HTML cache.

Usage: inject_lean_source.py SITE_DIR [PROJECT_ROOT]
"""
import html
import json
import re
import sys
from pathlib import Path

DIV_TOKEN = re.compile(r"<div\b|</div>")
DECL_OPEN = re.compile(r'<div class="declaration decl[^"]*" data-decl="([^"]+)"')
MARK = "bp_lean_source"

CSS = """
<style>
details.bp_lean_source { margin: 0; border-top: 1px solid var(--bp-color-border-soft, #ddd); }
details.bp_lean_source > summary { cursor: pointer; padding: 0.3rem 0.35rem; font-size: 0.72rem;
  color: var(--bp-color-text-muted, #666); user-select: none; }
details.bp_lean_source > summary:hover { color: var(--bp-color-text-strong, #000); }
details.bp_lean_source > pre { margin: 0; padding: 0.4rem 0.35rem; overflow-x: auto;
  font-size: 0.78rem; line-height: 1.35; white-space: pre; }
</style>
"""


def load_decls(manifest_path: Path):
    """Map canonical decl name -> (source path, first line, last line)."""
    decls = {}

    def walk(o):
        if isinstance(o, dict):
            prov = o.get("provenance", {})
            rng = o.get("range")
            name = o.get("canonical")
            src = None
            if isinstance(prov, dict):
                src = prov.get("inWorkspace", {}).get("sourcePath")
            if name and rng and src and name not in decls:
                decls[name] = (Path(src), rng["pos"][0], rng["endPos"][0])
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)

    walk(json.loads(manifest_path.read_text()))
    return decls


def source_block(decls, cache, name):
    if name not in decls:
        return None
    path, first, last = decls[name]
    if path not in cache:
        cache[path] = path.read_text().splitlines() if path.exists() else None
    lines = cache[path]
    if lines is None:
        return None
    text = "\n".join(lines[first - 1:last])
    return (
        f'<details class="{MARK}"><summary>Show Lean source (lines {first}–{last} of '
        f'{html.escape(path.name)})</summary>'
        f'<pre class="hl lean block"><code>{html.escape(text)}</code></pre></details>'
    )


def inject(doc: str, decls, cache) -> tuple[str, int]:
    if MARK in doc:
        return doc, 0
    out, pos, count = [], 0, 0
    for m in DECL_OPEN.finditer(doc):
        if m.start() < pos:
            continue
        block = source_block(decls, cache, m.group(1))
        if block is None:
            continue
        # find matching </div> of this declaration div
        depth = 0
        end = None
        for t in DIV_TOKEN.finditer(doc, m.start()):
            depth += 1 if t.group(0) != "</div>" else -1
            if depth == 0:
                end = t.start()
                break
        if end is None:
            continue
        out.append(doc[pos:end])
        out.append(block)
        pos = end
        count += 1
    out.append(doc[pos:])
    return "".join(out), count


def main():
    site = Path(sys.argv[1])
    manifest = next(site.rglob("blueprint-manifest.json"))
    data_dir = manifest.parent
    decls = load_decls(manifest)
    cache = {}
    total = 0

    for page in site.rglob("*.html"):
        doc = page.read_text()
        new, n = inject(doc, decls, cache)
        if n:
            if CSS not in new:
                new = new.replace("</head>", CSS + "</head>", 1)
            page.write_text(new)
            total += n

    cache_path = data_dir / "blueprint-html-cache.json"
    if cache_path.exists():
        c = json.loads(cache_path.read_text())
        n_cache = 0
        for entry in c.get("entries", []):
            new, n = inject(entry.get("html", ""), decls, cache)
            if n:
                entry["html"] = new
                n_cache += n
        cache_path.write_text(json.dumps(c, ensure_ascii=False))
        total += n_cache

    print(f"injected Lean source into {total} declaration boxes ({len(decls)} decls known)")


if __name__ == "__main__":
    main()
