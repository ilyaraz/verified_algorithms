#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$task_root"
./lake build
# Run the audit even when the build target is already cached.
./lake env lean Checks.lean
