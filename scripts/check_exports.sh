#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$task_root"
task_export_dir="$(mktemp -d)"
trap 'rm -rf -- "$task_export_dir"' EXIT
./lake env lean --run PerfectHashTools/Main.lean export "$task_export_dir/Generated.lean"
cmp PerfectHashTools/Generated.lean "$task_export_dir/Generated.lean"
# Parsing plus both equality theorems validates the exact serializer round trips.
./lake env lean "$task_export_dir/Generated.lean"
./lake env lean -s 131072 --run PerfectHashTools/Main.lean demo
