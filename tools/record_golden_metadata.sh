#!/usr/bin/env bash
# Plan §7 test 1: write tests/golden/METADATA after the golden sessions were run on the stock copy
# -- which tree produced the files, which dev patches that tree carried (the shared tree's patch
# status; the stock copy is its pre-edit twin), and the sha256 of every golden file.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
golden=$root/tests/golden
{
  echo "recorded: $(date -Is)"
  echo "tree: $root/Isabelle2025-2-stock (ISABELLE_IDENTIFIER=$(cat "$root/Isabelle2025-2-stock/etc/ISABELLE_IDENTIFIER"))"
  echo "isabelle: $("$root/tools/stock-isabelle" version)"
  echo "patch status of the shared tree at recording time (the stock copy carries the same dev patches; a dev patch reads CONFLICT once light's edits share its lines):"
  (cd "$root/../Isabelle2025-2" && my-better-isabelle status 2>&1 || true) | sed 's/^/  /'
  echo "sha256:"
  (cd "$golden" && sha256sum ./*.golden) | sed 's/^/  /'
} > "$golden/METADATA"
cat "$golden/METADATA"
