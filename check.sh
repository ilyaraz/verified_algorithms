#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$task_root"
./lake build
# Run the audit even when the build target is already cached.
./lake env lean Checks.lean
# Reexecute integration fixtures even when their compiled modules are cached.
./lake env lean -s 131072 DataStructures/PerfectHash/Total/Examples.lean
scripts/check_exports.sh
