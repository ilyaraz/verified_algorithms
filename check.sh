#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$task_root"
./lake build
# Run the audit even when the build target is already cached.
./lake env lean Checks.lean
# Recheck source and compiled recursion/capacity fixtures with cached artifacts.
./lake env lean RamLang/Examples.lean
./lake env lean RamLang/Compiler/Examples.lean
./lake env lean RamLang/Compiler/Proofs/Examples.lean
./lake env lean RamLang/Logic/Examples.lean
./lake env lean RamLang/DSL/Diagnostics.lean
./lake env lean RamLang/DSL/Examples.lean
./lake env lean RamLang/Library/Examples.lean
./lake env lean RamLang/RegisterOnly/Examples.lean
./lake env lean -s 131072 DataStructures/PerfectHash/Source/Query/Examples.lean
./lake env lean -s 131072 DataStructures/PerfectHash/Source/Components.lean
# Reexecute integration fixtures even when their compiled modules are cached.
./lake env lean -s 131072 DataStructures/PerfectHash/Total/Examples.lean
scripts/check_exports.sh
