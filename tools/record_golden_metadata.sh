#!/usr/bin/env bash
# Plan section 7 test 1: write tests/golden/METADATA after the golden sessions were recorded on
# light's stock tree (the tree without light, migration plan section 7) -- the tree, the commit it
# is detached at, its git status (must be empty), Isabelle's version there, and the sha256 of
# every golden file.  Usage: record_golden_metadata.sh [<stock tree>]
# (default: ../Isabelle2025-2-light_locale-stock next to this repository).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
golden=$root/tests/golden
tree=$(cd "${1:-$root/../Isabelle2025-2-light_locale-stock}" && pwd)
run_tree=$root/../my_better_isabelle_prover/tools/run-tree
status=$(git -C "$tree" status --porcelain --untracked-files=all)
[[ -z $status ]] || { echo "ERROR: $tree has uncommitted changes:" >&2; echo "$status" >&2; exit 1; }
{
  echo "recorded: $(date -Is)"
  echo "tree: $tree (ISABELLE_IDENTIFIER=$(cat "$tree/etc/ISABELLE_IDENTIFIER"))"
  echo "commit: $(git -C "$tree" rev-parse HEAD) ($(git -C "$tree" log -1 --format=%s))"
  echo "git status: empty"
  echo "isabelle: $("$run_tree" "$tree" version)"
  echo "sha256:"
  (cd "$golden" && sha256sum ./*.golden) | sed 's/^/  /'
} > "$golden/METADATA"
cat "$golden/METADATA"
