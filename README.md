# Verifiable algorithms

A Lean word-RAM model with finite assembly programs, wrapping arithmetic, mutable data memory, and a separate addressable read-only memory of independent uniform words.

The library supplies an executable interpreter, exact execution relations, cost and memory-preservation proofs, and a finite probability model for random memory.

Read the [word RAM reference](docs/word-ram.md) for the complete machine definition, instruction set, probability semantics, theorem guide, and examples.

The [perfect hashing roadmap](docs/perfect-hashing-plan.md) plans a modular static membership dictionary with repeated-input support, explicit resource bounds, and executable certified programs.

M0's [static dictionary contract](docs/perfect-hashing-spec.md) is implemented in `DataStructures`: calling conventions, explicit admissibility predicates, a full correctness/resource target, and proved feasible layouts. M1 adds logical right shift, reusable memory/block assertions, labelled assembly with proved relocation, and verified fill/copy/traversal loops. M2 supplies the [verified multiply-shift family](docs/hashing.md), sampler, finite enumeration, and constant-cost RAM evaluator. M3 adds [finite retry/fallback proofs and random-block law transfer](docs/finite-search.md). M4 supplies [verified expected-linear deduplication](docs/deduplication.md), including arbitrary repetitions and dirty memory. The perfect-hash dictionary programs remain later milestones.

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

After bootstrap, checks work offline. If Lean is managed through Elan instead, the committed `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` also support standard Lake commands:

```sh
lake exe cache get
lake build
lake env lean Checks.lean
```

Import `WordRam` for the complete library, or `WordRam.Properties` for the executable machine and its core proofs without Mathlib probability imports. [Examples](WordRam/Examples.lean) contain small verified programs; [Checks.lean](Checks.lean) checks probability examples and audits proof dependencies.
