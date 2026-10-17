#!/usr/bin/env bash
# Plan §8 step 0 (b)/(c).  `--before` (run once, before the first edit): the stock copy's src/ and
# etc/ must be file-for-file identical to the shared tree's (etc/ISABELLE_IDENTIFIER excepted), and
# the patch tool's status is recorded as the baseline.  Without `--before`: every file that differs
# between the two trees must be listed in tools/patched_files.txt, and the patch tool's status must
# still equal the baseline (someone unapplying a dev patch meanwhile would leak into our patches).
# The baseline was re-recorded once (2026-10-15, plan §11 (6) D1 and (32)): milestone 2 edits
# term_to_ast in syntax_phases.ML, where the dev patch show_types_nv has its hunks, so the tool
# reports that patch as CONFLICT although its lines are all still there (attrib.ML, the other
# dev-patched file, still reads applied); make_patches.sh proves the lines are there at the end
# (plan §8 step 5).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
shared=$root/../Isabelle2025-2
stock=$root/Isabelle2025-2-stock
baseline=$root/tools/patch_status_baseline.txt

status() { (cd "$shared" && my-better-isabelle status 2>&1 || true); }

# diff may only report differences (status 1); trouble (a missing directory, an unreadable file)
# aborts the run
raw=$(for d in src etc; do
  LC_ALL=C diff -rq "$stock/$d" "$shared/$d" || (( $? == 1 )) || { echo "ERROR: diff failed on $d/" >&2; exit 2; }
done)

changed() {  # paths (relative to the tree root) of files that differ between the two trees
  sed -E "s#^Files $stock/(.*) and .* differ\$#\\1#; s#^Only in $shared/([^:]*): (.*)\$#\\1/\\2#; s#^Only in $stock/([^:]*): (.*)\$#\\1/\\2 (missing in shared tree)#" <<<"$raw" \
    | /usr/bin/grep -vx 'etc/ISABELLE_IDENTIFIER' || true
}

if [[ ${1:-} == --before ]]; then
  if [[ -n $(changed) ]]; then
    changed; echo "ERROR: stock copy differs from the shared tree before the first edit" >&2; exit 1
  fi
  status > "$baseline"
  echo "stock copy identical to the shared tree; patch status baseline recorded in $baseline"
else
  allowed=$(/usr/bin/grep -v '^[[:space:]]*\(#\|$\)' "$root/tools/patched_files.txt")
  bad=0
  while read -r f; do
    [[ -z $f ]] && continue
    if /usr/bin/grep -qxF "$f" <<<"$allowed"; then echo "changed  $f"
    else echo "ERROR: not an allowed difference (tools/patched_files.txt): $f" >&2; bad=1; fi
  done <<<"$(changed)"
  if ! diff <(status) "$baseline" >/dev/null; then
    echo "ERROR: patch tool status differs from the baseline:" >&2; diff <(status) "$baseline" >&2 || true; bad=1
  fi
  exit $bad
fi
