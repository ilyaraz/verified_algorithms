# Verifiable algorithms

A Lean word-RAM library with an executable, certified static membership dictionary
using two-level perfect hashing. Its fixed 238-instruction constructor accepts
repeated full-word keys and terminates successfully for every random-memory
image. Under the finite uniform random-memory law, preprocessing takes at most
`10000*(N+1)` expected instructions. Queries take at most 33 instructions; the
retained dictionary uses at most `64*(d+1)` words, where `N` counts occurrences
and `d` counts distinct keys.

The [public certificate](DataStructures/PerfectHash/Certified.lean) proves the
[original contract](docs/perfect-hashing-spec.md), including explicit memory-fit
assumptions, dirty initial memory, peak space, random reads, and queries after
overwriting all unretained memory. The [completed M0–M11 plan](docs/perfect-hashing-plan.md)
and [audit guide](docs/perfect-hashing-audit.md) explain the proof structure and
verification coverage.

The [paper (PDF)](docs/perfect-hashing-paper.pdf) gives a compact existence
theorem with the necessary definitions, explicit resource bounds, and probability
guarantees. Its [LaTeX source](docs/perfect-hashing-paper.tex) can be rebuilt with
`./scripts/build_paper.sh` using Tectonic, latexmk, or pdflatex.

```lean
import DataStructures.PerfectHash.Certified

#check PerfectHash.fksCode_correct
#check PerfectHash.certified_query_after_build
#check PerfectHash.dictionary_algorithms_exist
```

The underlying machine has wrapping arithmetic, unit-cost multiplication,
remainder and logical right shift, mutable data memory, and separate immutable
addressed random memory. The [word RAM reference](docs/word-ram.md) defines its
semantics, interpreter, execution costs, and probability model.

| Component | Reference |
| --- | --- |
| Full-word hashing and finite search | [Multiply-shift](docs/hashing.md), [retry and fallback](docs/finite-search.md) |
| Repeated-input processing and FKS mathematics | [Deduplication](docs/deduplication.md), [abstract construction](docs/fks-abstract.md) |
| Retained format and query | [Layout and constant-time query](docs/perfect-hashing-query.md) |
| Concrete preprocessing | [Trial blocks](docs/perfect-hashing-trials.md), [bounded constructor](docs/perfect-hashing-bounded.md), [total constructor and bounds](docs/perfect-hashing-total.md) |
| Executable interface | [Certificate, demo, and checked source export](docs/perfect-hashing-export.md) |

The [Lean Atlas website](website/README.md) provides an interactive dependency diagram,
plain-language descriptions of every authored definition and statement, and links to
line-numbered Lean source. Build it after bootstrap with:

```sh
python3 scripts/build_website.py
```

Open `website/dist/index.html` directly in a browser, or serve `website/dist/` with
any static web server. No JavaScript packages or external services are needed to
build or browse the atlas.

On Linux x86-64, bootstrap the pinned Lean 4.24.0 toolchain and Mathlib dependencies, then build and check:

```sh
./bootstrap.sh
./check.sh
```

After bootstrap, checks work offline. `./check.sh` builds all targets, audits proof
and executable dependencies, reruns the total-constructor boundary/fallback
fixtures, validates regenerated program exports, and runs the demo. Run the demo
on its own with:

```sh
./lake env lean -s 131072 --run PerfectHashTools/Main.lean demo
```

If Lean is managed through Elan instead, the committed `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` also support standard Lake commands:

```sh
lake exe cache get
lake build
lake env lean Checks.lean
```

Import `DataStructures` for the certified dictionary, `WordRam` for the complete
machine library, or `WordRam.Properties` for the executable machine and its core
proofs without Mathlib probability imports. [Examples](WordRam/Examples.lean)
contain small verified programs; [Checks.lean](Checks.lean) checks probability
examples and audits proof dependencies.

The alternative [structured word-RAM development](docs/ramlang-contract.md)
adds an independent recursive source language under `RamLang/`. Its milestone
ledger tracks the compiler, source proof interface, and separate perfect-hashing
integration. Import `RamLang` for the checked core, source evaluator, recursive
compiler, and proofs. Finite source derivations transfer to exact target
instruction counts, application traces, and stack bounds, including exhaustion.
Productive loop certificates also establish infinite target runs with bounded
stack use. Total source contracts prove recursive sum and iterative array fill,
including instruction bounds, stack use, and memory preservation. The
[C-like DSL](docs/ramlang-dsl.md) supports named recursive functions, rich
expressions, diagnostics, and verified fill/copy/traversal/retry routines. The
register-only backend verifies a checked straight-line subset with helper
inlining and full trace preservation. The separate [source perfect-hashing implementation](docs/perfect-hashing-source.md)
proves membership through ordinary helper calls, with at most 237 instructions
and 28 stack words. Its construction components now verify sampling, rounding,
deduplication, root/child trials, and allocation against the original models,
with explicit instruction and stack bounds. The 1,720-instruction source bounded
constructor preserves the original nine-register build interface and proves
normal success or retry-budget failure, safe prefixes, fresh addressed samples,
and queries after overwriting unretained storage. Its stack is inside the existing
scratch reservation. The 1,842-instruction total constructor adds deterministic
odd-seed fallback and proves success for every random image, expected linear
actual instruction work, linear retained/peak space, and the same constant-time
query. All L0–L7 and P0–P3 milestones are complete. The original assembly programs
and proofs remain intact.
