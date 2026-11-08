#!/usr/bin/env bash
# Compile the concise, verified perfect-hashing existence theorem.
# Usage: ./scripts/build_paper.sh
# Requires Tectonic, latexmk, or pdflatex. A locally downloaded Tectonic may
# be placed at .toolchain/tectonic/tectonic without changing the system.
set -euo pipefail
paper_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
paper_source="$paper_root/docs/perfect-hashing-paper.tex"
paper_build="$(mktemp -d "${TMPDIR:-/tmp}/perfect-hashing-paper.XXXXXXXX")"
trap 'rm -rf "$paper_build"' EXIT

if command -v tectonic >/dev/null 2>&1; then
  tectonic --keep-logs --outdir "$paper_build" "$paper_source"
elif [[ -x "$paper_root/.toolchain/tectonic/tectonic" ]]; then
  "$paper_root/.toolchain/tectonic/tectonic" --keep-logs --outdir "$paper_build" "$paper_source"
elif command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir="$paper_build" "$paper_source"
elif command -v pdflatex >/dev/null 2>&1; then
  for paper_pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$paper_build" "$paper_source"
  done
else
  printf '%s\n' 'Install Tectonic, latexmk, or pdflatex to compile the paper.' >&2
  exit 1
fi

paper_log="$paper_build/perfect-hashing-paper.log"
if [[ -f "$paper_log" ]] && rg -n \
  'undefined references|undefined citations|Reference .* undefined|Citation .* undefined|Overfull \\hbox|Overfull \\vbox' \
  "$paper_log"; then
  printf '%s\n' 'Compilation left unresolved references or layout overflow; review the messages above.' >&2
  exit 1
fi
cp "$paper_build/perfect-hashing-paper.pdf" "$paper_root/docs/perfect-hashing-paper.pdf"
printf 'Built %s\n' "$paper_root/docs/perfect-hashing-paper.pdf"
