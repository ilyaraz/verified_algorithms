#!/usr/bin/env python3
"""Build the offline Lean atlas. Requires Python 3 and the pinned Lean toolchain."""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "website"
OUT = SITE / "dist"
CACHE = ROOT / ".lake/website"
MODULES = ["Word", "Memory", "Program", "Machine", "Execution", "Properties", "Random", "Examples"]
FILES = [Path("WordRam") / f"{m}.lean" for m in MODULES] + [Path("Checks.lean")]


def mask_comments(source: str) -> str:
    """Preserve offsets, including nested Lean comments and quoted strings."""
    out = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
            elif pair == "-/":
                depth -= 1
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
                continue
            out[i:i + 2] = "  "
            i += 2
        elif quoted:
            if source[i] == "\\":
                i += 2
            else:
                quoted = source[i] != '"'
                i += 1
        elif pair == "/-":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        else:
            quoted = source[i] == '"'
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(out)


def authored_declarations():
    declarations = []
    pattern = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(private|protected|noncomputable)\s+)?"
                         r"(abbrev|def|theorem|lemma|structure|inductive|instance|opaque|axiom|class|example)\b\s*([^\s(:{]+)?")
    for file in FILES:
        source = (ROOT / file).read_text()
        namespace = []
        for line, text in enumerate(mask_comments(source).splitlines(), 1):
            if text.startswith("namespace "):
                namespace.append(text.split()[1])
            elif re.match(r"(?:noncomputable )?section\b", text):
                namespace.append("")
            elif re.match(r"end\b", text) and namespace:
                namespace.pop()
            match = pattern.match(text)
            if not match:
                continue
            modifier, kind, name = match.groups()
            if kind == "example":
                name = f"example_{line}"
                full_name = f"Checks.{name}"
            else:
                if not name:
                    raise ValueError(f"Unnamed {kind} at {file}:{line} needs an explicit export name")
                full_name = ".".join([p for p in namespace if p] + [name])
            declarations.append(dict(id=full_name, name=name, kind=kind,
                category="statement" if kind in {"theorem", "lemma", "axiom", "example"} else "definition",
                file=file.as_posix(), module=file.stem, line=line, private=modifier == "private"))
    return declarations


def public_name(name):
    return re.sub(r"^_private\..*?\.\d+\.", "", name)


def extract(render_only=False):
    CACHE.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(b"".join((ROOT / f).read_bytes() for f in FILES) +
                            (ROOT / "scripts/ExtractGraph.lean").read_bytes()).hexdigest()
    stamp = CACHE / "fingerprint"
    if render_only:
        if not stamp.exists() or stamp.read_text() != digest:
            raise SystemExit("Lean sources changed. Run the build without --render-only.")
    else:
        subprocess.run([str(ROOT / "lake"), "build"], cwd=ROOT, check=True)
        source = (ROOT / "Checks.lean").read_text()
        # Temporary names retain original line numbers and proof bodies.
        source = re.sub(r"^example\b", lambda m: "theorem WebsiteExample" +
                        str(source[:m.start()].count("\n") + 1), source, flags=re.M)
        (CACHE / "Extract.lean").write_text(source + "\n" + (ROOT / "scripts/ExtractGraph.lean").read_text())
        subprocess.run([str(ROOT / "lake"), "env", "lean", str(CACHE / "Extract.lean")], cwd=ROOT, check=True)
        stamp.write_text(digest)
    return json.loads((CACHE / "declarations.json").read_text()), digest


def make_graph(raw, descriptions):
    nodes = authored_declarations()
    by_id = {n["id"]: n for n in nodes}
    normalized = {public_name(r["name"]): r for r in raw}
    for node in nodes:
        raw_name = f"WebsiteExample{node['line']}" if node["kind"] == "example" else node["id"]
        row = normalized.get(raw_name)
        if not row or row["line"] != node["line"]:
            raise ValueError(f"No matching Lean declaration at {node['file']}:{node['line']} ({raw_name})")
        node["endLine"] = row["endLine"]
        node["description"] = descriptions.get(node["id"], "")
        if not node["description"]:
            raise ValueError(f"Missing natural-language description: {node['id']}")
        node["source"] = "\n".join((ROOT / node["file"]).read_text().splitlines()[node["line"] - 1:node["endLine"]])
        node["sourceUrl"] = f"source/{node['file']}.html#L{node['line']}"
        node["leanUrl"] = f"source/{node['file']}"
        node["rawName"] = row["name"]

    owner = {n["rawName"]: n["id"] for n in nodes}
    # Constructors, projections, recursors and generated helpers belong to their
    # authored declaration. Nested authored declarations always win.
    for row in raw:
        if row["name"] in owner:
            continue
        name = public_name(row["name"])
        parents = [key for key in by_id if name.startswith(key + ".")]
        if parents:
            owner[row["name"]] = max(parents, key=len)
        elif row["line"]:
            file = row["module"].replace(".", "/") + ".lean"
            containing = [n for n in nodes if n["file"] == file and n["line"] <= row["line"] <= n["endLine"]]
            if containing:
                owner[row["name"]] = min(containing, key=lambda n: n["endLine"] - n["line"])["id"]

    edges = {}
    raw_map = {r["name"]: r for r in raw}

    def resolve(name, seen=None):
        if name in owner:
            return {owner[name]}
        seen = set() if seen is None else seen
        if name in seen or name not in raw_map:
            return set()
        seen.add(name)
        row = raw_map[name]
        return set().union(*(resolve(dep, seen) for dep in row["typeDeps"] + row["valueDeps"]))

    for row in raw:
        dependent = owner.get(row["name"])
        if not dependent:
            continue
        for field, role in [("typeDeps", "type"), ("valueDeps", "body")]:
            for reference in row[field]:
                for dependency in resolve(reference):
                    if dependent != dependency:
                        edges.setdefault((dependency, dependent), set()).add(role)
    for node in nodes:
        node.pop("rawName")
        node["dependencies"] = sorted(a for a, b in edges if b == node["id"])
        node["dependents"] = sorted(b for a, b in edges if a == node["id"])
    return nodes, [dict(source=a, target=b, roles=sorted(roles)) for (a, b), roles in sorted(edges.items())]


def render_sources():
    for file in FILES + [Path("WordRam.lean")]:
        text = (ROOT / file).read_text()
        destination = OUT / "source" / file
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
        prefix = "../" * (len(file.parts))
        rows = "\n".join(f'<tr id="L{i}"><td><a href="#L{i}">{i}</a></td><td><code>{html.escape(line)}</code></td></tr>'
                         for i, line in enumerate(text.splitlines(), 1))
        page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{file} · Lean Atlas</title><link rel="stylesheet" href="{prefix}source.css"></head>
<body><header><a href="{prefix}index.html">← Lean Atlas</a><strong>{file}</strong>
<a href="{file.name}" download>Download .lean ↗</a></header>
<main><p>Exact source snapshot · select a line number to link to it.</p><table aria-label="Lean source"><tbody>{rows}</tbody></table></main>
<script src="{prefix}source.js"></script></body></html>'''
        destination.with_suffix(".lean.html").write_text(page)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--render-only", action="store_true", help="Reuse extraction only when Lean inputs are unchanged")
    args = parser.parse_args()
    raw, fingerprint = extract(args.render_only)
    descriptions = json.loads((SITE / "descriptions.json").read_text())
    nodes, edges = make_graph(raw, descriptions)
    OUT.mkdir(parents=True, exist_ok=True)
    for file in (SITE / "assets").iterdir():
        if file.is_file():
            shutil.copy2(file, OUT / file.name)
    data = dict(nodes=nodes, edges=edges, modules=MODULES + ["Checks"], fingerprint=fingerprint,
        method="References in Lean-elaborated types and bodies. Generated constructors, fields, recursors and helpers are grouped into their authored declaration. External libraries are omitted.")
    (OUT / "graph.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    # A classic script keeps file:// browsing functional, without fetch or a CDN.
    (OUT / "graph-data.js").write_text("window.LEAN_GRAPH = " + json.dumps(data, ensure_ascii=False).replace("</", "<\\/") + ";\n")
    render_sources()
    print(f"Built {OUT}: {len(nodes)} declarations, {len(edges)} dependency edges, {len(FILES)} source modules.")


if __name__ == "__main__":
    main()
