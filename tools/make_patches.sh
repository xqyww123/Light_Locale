#!/usr/bin/env bash
# Plan §8 step 5.  The files under patches/Isabelle2025-2/ are the only record of light locale's
# changes to the Isabelle tree: one `diff -ruN` of the stock copy's src/ against the shared tree's,
# split per file (file name = the path with `/` written `-`), header timestamps dropped except the
# epoch one that marks a new file (patch creates and removes the file by it).  Then the checks of that step:
# the differing set is within tools/patched_files.txt (check_stock_diff.sh), no residue of the
# timing patch, a round trip on a sparse copy of the stock copy (forward reproduces the shared
# tree, backward the stock copy, byte for byte, new files created and removed), the same round
# trip on a sparse pristine checkout when `--pristine <hg repo>` names one (tag = the directory
# name; the stock copy carries the dev patches, so offsets are allowed there, fuzz never), and
# the signature sections of every patched .ML file only gain entries.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
shared=$root/../Isabelle2025-2
stock=$root/Isabelle2025-2-stock
out=$root/patches/Isabelle2025-2
tag=$(basename "$out")
pristine_repo=; [[ ${1:-} == --pristine ]] && pristine_repo=$2

"$root/tools/check_stock_diff.sh" > /dev/null

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
ln -s "$stock" "$work/a"; ln -s "$shared" "$work/b"
set +e; (cd "$work" && TZ=UTC LC_ALL=C diff -ruN a/src b/src > all.diff); rc=$?; set -e
[[ $rc == 1 ]] || { echo "ERROR: diff exit $rc (0 = no difference at all)" >&2; exit 1; }

mkdir -p "$out"; rm -f "$out"/*.patch
awk -v out="$out" '
  /^diff -ruN / { name = $3; sub(/^a\//, "", name); gsub("/", "-", name); file = out "/" name ".patch" }
  /^(---|\+\+\+) / && !/\t1970-01-01 / { sub(/\t.*/, "") }
  { print > file }' "$work/all.diff"
files=$(sed -n 's#^diff -ruN a/\(.*\) b/.*#\1#p' "$work/all.diff")
echo "$(wc -l <<<"$files") patch files written to $out"

if /usr/bin/grep -l 'locale_notes_flagged\|add_facts_flagged' "$out"/*.patch; then
  echo "ERROR: residue of the timing patch in the patches above" >&2; exit 1
fi

# sparse copy of a tree: only the files the patches touch; `fetch <path> <dest>` fails if absent
sparse() {
  local dir=$1 fetch=$2 f
  for f in $files; do
    mkdir -p "$dir/$(dirname "$f")"
    "$fetch" "$f" "$dir/$f" 2> /dev/null || rm -f "$dir/$f"
  done
}
from_stock() { cp "$stock/$1" "$2"; }
from_shared() { cp "$shared/$1" "$2"; }
from_hg() { (cd "$pristine_repo" && hg cat -r "$tag" "$1") > "$2"; }
same_trees() { LC_ALL=C diff -r "$1" "$2" > /dev/null || { echo "ERROR: $3" >&2; exit 1; }; }

# apply all patches in $1 (forward, or backward with -R); fuzz is never allowed
apply() { (cd "$1" && cat "$out"/*.patch | patch -p1 -F0 --no-backup-if-mismatch "${@:2}"); }

# round trip on the stock copy: forward = the shared tree (offset-free), backward = the stock copy
sparse "$work/stock0" from_stock; cp -r "$work/stock0" "$work/stock"; sparse "$work/shared" from_shared
apply "$work/stock" --dry-run > /dev/null
apply "$work/stock" > "$work/forward.log"
if /usr/bin/grep -q 'offset\|fuzz' "$work/forward.log"; then
  echo "ERROR: offset or fuzz against the stock copy:" >&2; cat "$work/forward.log" >&2; exit 1
fi
same_trees "$work/stock" "$work/shared" "forward application does not reproduce the shared tree"
apply "$work/stock" -R > /dev/null
same_trees "$work/stock" "$work/stock0" "backward application does not reproduce the stock copy"
echo "round trip on the stock copy: ok"

# the same on a pristine checkout, where the dev patches' hunks are absent
if [[ -n $pristine_repo ]]; then
  sparse "$work/pristine0" from_hg; cp -r "$work/pristine0" "$work/pristine"
  apply "$work/pristine" > "$work/pristine.log"
  /usr/bin/grep 'offset' "$work/pristine.log" || true
  apply "$work/pristine" -R > /dev/null
  same_trees "$work/pristine" "$work/pristine0" "backward application does not reproduce the pristine tree"
  echo "round trip on the pristine tree ($pristine_repo, tag $tag): ok"
fi

# signature sections (Isabelle style: `signature NAME =` ... `end` at column 0) only gain entries
sigs() { [[ -e $1 ]] && awk '/^signature [A-Z_0-9]+ *=/ {p = 1} p {print} p && /^end;?[[:space:]]*$/ {p = 0}' "$1" || true; }
bad=0
for f in $files; do
  [[ $f == *.ML ]] || continue
  d=$(LC_ALL=C diff <(sigs "$stock/$f") <(sigs "$shared/$f") || true)
  if /usr/bin/grep -q '^<' <<<"$d"; then
    echo "ERROR: a signature entry of $f changed or disappeared:" >&2; echo "$d" >&2; bad=1
  else
    sed -n "s#^> #signature +  $f: #p" <<<"$d"
  fi
done
exit $bad
