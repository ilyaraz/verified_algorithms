# Lean Atlas

A static, offline-capable browser for the Word RAM formalization and completed
certified perfect-hash dictionary, the independent recursive RamLang language,
and executable export tools. It
includes all authored declarations in the library, tools, and checks, with distinct
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
Lean declaration. The root `WordRam.lean` and `DataStructures.lean` files contain
imports only, and their source is also exported.

Handwritten explanations live in `descriptions.json`, keyed by full declaration
name. The build fails if an authored declaration lacks a description or cannot
be matched to Lean’s source-location metadata. New modules should be added to
`FILES` in the builder and imported by the check target. Nested dictionary modules
use distinct labels such as `StaticSet.Specification` and `PerfectHash.Specification`.
Tool modules use labels such as `PerfectHashTools.Export` and
`PerfectHashTools.Generated`; the extractor includes the `PerfectHashTools`
module root as well as the mathematical libraries.
Rebuild after changing
Lean files or descriptions; generated output is ignored by Git. For frontend-only
edits, `--render-only` reuses the extraction only if the Lean input fingerprint
still matches.

Every source link opens a line-numbered HTML snapshot with a stable `#L<number>`
anchor; the original `.lean` file is downloadable from that page. The inspector
shows the exact declaration text. There is no dependency on a Git hosting service.
Declaration selection, graph view, module, and kind filters are shareable in the
URL fragment. Search applies to the index; module and kind filters apply to both
the index and graph. The inspector always lists all of a declaration’s neighbors.

## Reviewing the dictionary

Search for `PerfectHash.certifiedFKS`, then follow its dependencies through
`fksCode_correct` to `PerfectHash.Total.specification`. That contract combines
construction correctness, expected resources, and the representation-based query
theorem. `certified_query_after_build` provides the public build/query statement
with workspace overwrite allowed. The [audit guide](../docs/perfect-hashing-audit.md)
lists the assumptions and resource proof paths.

The nodes `PerfectHash.Exported.preprocess_roundtrip` and
`PerfectHash.Exported.query_roundtrip` connect the generated literal arrays to
the same `fksCode` used by the certificate. These dependencies come from Lean's
elaborated equality proofs. Atlas tests check these paths alongside the complete
declaration inventory, source snapshots, anchors, and reverse dependency index.

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

## Structured language milestones

The published `ramlang.html` page mirrors the [ABI contract and milestone ledger](../docs/ramlang-contract.md).
RamLang modules have distinct `RamLang.*` labels and import only the reusable
machine library. Search for `RamLang.step_ideal_of_fits` and
`RamLang.Examples.spin_diverges` to inspect source semantics and capacity proofs.
The ledger explicitly separates completed milestones from remaining work.

For the executable baseline compiler, inspect `RamLang.Compiler.compile`,
`RamLang.Compiler.compile_code_size`, and `RamLang.Compiler.Examples.sum_exact_fit`.
For the general compiler proofs, inspect `RamLang.Compiler.compile_evaluation`,
`RamLang.Compiler.compiled_returns`, and `RamLang.Compiler.compiled_loop_diverges`.
Source derivations yield exact target instruction costs, application traces,
intermediate stack bounds, exhaustion behavior, and interrupted-prefix safety.
The theorem-based fixtures in `RamLang.Compiler.ProofExamples` exercise these
results from dirty RAM without expanding a target execution by computation.

For source verification, inspect `RamLang.Logic.while_total`,
`RamLang.Logic.Contract.call`, and `RamLang.Logic.Contract.compiled`.
`RamLang.Logic.Sum.compiled_correct` proves exact recursive time and stack use;
`RamLang.Logic.Fill.compiled_correct` transfers an invariant-based array proof
to the generated program, including memory preservation and prefix policies.

The [C-like language guide](../docs/ramlang-dsl.md) is published as `ramlang-dsl.html`.
Search for `RamLang.DSL.Examples.sum_core` to connect readable source with its
verified core, `RamLang.Library.Copy.compiled_correct` for array traversal,
and `RamLang.Library.FirstNonzero.compiled_correct` for bounded retry with a
proved fresh sample schedule. `RamLang.report` displays the generated code.

`RamLang.RegisterOnly.compile` checks an alternate straight-line subset and its
register budget. Its `compiled_returns` theorem preserves the full source trace;
`compiled_readOnly` forbids writes at every target prefix for read-only source
proofs. The overlap example verifies argument permutations and caller locals
across inline calls in fifteen instructions without stack memory.

The separate source perfect-hashing guide is published as `perfect-hashing-source.html`.
Inspect `PerfectHash.Source.Query.program`, `contract`, `execution`, and `spec` to
follow the C-like query from table invariants to generated machine execution.
Its 237-instruction bound includes helper calls and halt; its 28-word stack is
separated from the retained dictionary, and every interrupted prefix is safe.

## Reviewing the alternative source constructor

Search for `PerfectHash.Source.Bounded.execution` and
`PerfectHash.Source.Bounded.query_after_build`. Their dependencies connect the
C-like program, compositional source contracts, generic compiler transfer,
public entry adapter and retained representation. The source implementation
remains under `Source/`; the original assembly certificate remains available.
The source guide documents the new numerical bounds and explicit code-fit
condition. Tests cover these proof paths as well as all source snapshots.

For the completed total constructor, start at
`PerfectHash.Source.Total.specification`, then inspect `execution`,
`expected_instructions`, and `query_after_build`. The enumeration rule lives in
`RamLang.Library.Enumeration.loop_contract`; its two source instantiations use
finite successful candidate prefixes to prove termination without a runtime
search bound. `Total.work_le_model` connects the source instruction allowance
to the pure probability model. The Atlas tests require these source/compiler
and expectation edges while retaining the original assembly proof paths.
