# Verifiable algorithms

A Lean word-RAM model with finite assembly programs, wrapping arithmetic, mutable data memory, and a separate addressable read-only memory of independent uniform words.

The library supplies an executable interpreter, exact execution relations, cost and memory-preservation proofs, and a finite probability model for random memory.

Read the [word RAM reference](docs/word-ram.md) for the complete machine definition, instruction set, probability semantics, theorem guide, and examples.

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
