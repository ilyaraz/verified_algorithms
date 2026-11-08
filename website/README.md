# Lean Atlas

A static, offline-capable browser for the Word RAM formalization. It includes all
161 authored declarations in the current library and checks, with distinct
definition/statement shapes and colors, natural-language descriptions, a full
dependency diagram, focused neighborhoods, search, filters, and exact source links.

From the repository root, after `./bootstrap.sh`:

```sh
python3 scripts/build_website.py
python3 -m http.server 8000 --directory website/dist
```

Visit <http://localhost:8000>, or open `website/dist/index.html` directly. The
generated directory can be uploaded unchanged to any static host. There are no
runtime dependencies, remote fonts, CDN assets, analytics, or API calls.

## How the graph is built

`scripts/build_website.py` builds the Lean project, then runs
`scripts/ExtractGraph.lean` appended to a temporary copy of `Checks.lean`. Unnamed
examples receive temporary names in that copy so their elaborated proofs can be
inspected. Source files and proof bodies are unchanged, and original source line
numbers are preserved. The temporary files stay under `.lake/website/`.

The extractor reads constants referenced by elaborated types and bodies, including
proofs, implicit arguments, and typeclass instances. Constructors, structure
fields, recursors, derived instances, and generated helpers are grouped into their
authored parent declaration. References from those grouped constants are retained.
References to external Lean/Std/Mathlib declarations are omitted. This is a graph
of elaborated references, not a record of every tactic name or an assertion that
each edge is logically necessary. An arrow goes **from dependency to user**.

Definitions include proposition-valued definitions and inductive relations such
as `Step` and `Steps`; statements are proved theorems and examples. Private
definitions are included. Constructors and fields are visible in their parent’s
Lean declaration. The root `WordRam.lean` file contains imports only, and its
source is also exported.

Handwritten explanations live in `descriptions.json`, keyed by full declaration
name. The build fails if an authored declaration lacks a description or cannot
be matched to Lean’s source-location metadata. New modules should be added to
`MODULES` in the builder and imported by the check target. Rebuild after changing
Lean files or descriptions; generated output is ignored by Git. For frontend-only
edits, `--render-only` reuses the extraction only if the Lean input fingerprint
still matches.

Every source link opens a line-numbered HTML snapshot with a stable `#L<number>`
anchor; the original `.lean` file is downloadable from that page. The inspector
shows the exact declaration text. There is no dependency on a Git hosting service.
Declaration selection, graph view, module, and kind filters are shareable in the
URL fragment. Search applies to the index; module and kind filters apply to both
the index and graph. The inspector always lists all of a declaration’s neighbors.

## Validation

```sh
python3 -m unittest discover -s scripts -p 'test_website.py' -v
node --check website/assets/app.js
```

The optional browser smoke test uses Playwright (only for testing, never shipped):

```sh
npm install --prefix /tmp/lean-atlas-qa playwright
# Install a browser if Playwright's Chromium is not already available:
/tmp/lean-atlas-qa/node_modules/.bin/playwright install chromium
PLAYWRIGHT_MODULE=/tmp/lean-atlas-qa/node_modules/playwright/index.mjs \
  node scripts/test_website.mjs
```

`ATLAS_URL` can point the smoke test at a local HTTP server. It defaults to the
local `file://` build. `CHROMIUM_EXECUTABLE` can select an existing Chromium binary.

The `.openai/hosting.json` manifest records the optional owner-private Sites
deployment. It is not needed for local browsing or hosting elsewhere.
