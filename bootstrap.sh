#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_version=4.24.0
task_archive="lean-${task_version}-linux.tar.zst"
task_sha=b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec
task_dest="$task_root/.toolchain/lean-${task_version}-linux"
if [[ ! -x "$task_dest/bin/lean" ]]; then
  mkdir -p "$task_root/.downloads" "$task_root/.toolchain"
  if [[ ! -f "$task_root/.downloads/$task_archive" ]]; then
    curl --fail --silent --show-error --location --retry 3 \
      "https://github.com/leanprover/lean4/releases/download/v${task_version}/${task_archive}" \
      --output "$task_root/.downloads/$task_archive.part"
    mv "$task_root/.downloads/$task_archive.part" "$task_root/.downloads/$task_archive"
  fi
  printf '%s  %s\n' "$task_sha" "$task_root/.downloads/$task_archive" | sha256sum --check
  tar --zstd -xf "$task_root/.downloads/$task_archive" -C "$task_root/.toolchain"
fi
"$task_dest/bin/lean" --version
"$task_root/lake" exe cache get
