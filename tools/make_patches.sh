#!/usr/bin/env bash
# Plan §8 step 5.  The files under patches/Isabelle2025-2/ are the only record of light locale's
# changes to the Isabelle tree: one `diff -ruN` of the stock copy's src/ against the shared tree's,
# split per file (file name = the path with `/` written `-`), header timestamps dropped except the
# epoch one that marks a new file (patch creates and removes the file by it).  Then the checks of
# that step: the patched files are exactly the files check_stock_diff.sh reports (hence within
# tools/patched_files.txt), no residue of the timing patch, a round trip on a sparse copy of the
# stock copy (forward reproduces the shared tree, backward the stock copy, byte for byte, new files
# created and removed), the same round trip on a sparse pristine checkout (tag = the directory
# name, from the hg clone plan §8 step 0 (d) names unless `--pristine <hg repo>` says otherwise;
# the stock copy carries the dev patches, so offsets are allowed there, fuzz never), and the
# signature sections of every patched .ML file keep every stock entry unchanged and gain exactly
# the entries whose heads (path, signature, keyword, name; not the type) are listed in
# tools/signature_additions.txt.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
shared=$root/../Isabelle2025-2
stock=$root/Isabelle2025-2-stock
out=$root/patches/Isabelle2025-2
tag=$(basename "$out")
usage() { echo "usage: $0 [--pristine <hg repo>]" >&2; exit 2; }
case $#:${1:-} in
  0:) pristine_repo=$HOME/isa_release_proto/isabelle-src ;;
  2:--pristine) pristine_repo=$2 ;;
  *) usage ;;
esac
[[ -n $pristine_repo ]] || usage
hg -R "$pristine_repo" id -r "tag('$tag')" > /dev/null \
  || { echo "ERROR: $pristine_repo is not an hg repository with tag $tag" >&2; exit 1; }

changed=$("$root/tools/check_stock_diff.sh" | sed -n 's/^changed  //p')

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
ln -s "$stock" "$work/a"; ln -s "$shared" "$work/b"
set +e; (cd "$work" && TZ=UTC LC_ALL=C diff -ruN a/src b/src > all.diff); rc=$?; set -e
[[ $rc == 1 ]] || { echo "ERROR: diff exit $rc (0 = no difference at all)" >&2; exit 1; }

# the two header lines after each `diff` line lose their timestamps; hunk body lines are left alone
mkdir -p "$out"; rm -f "$out"/*.patch
awk -v out="$out" '
  /^diff -ruN / { name = $3; sub(/^a\//, "", name); gsub("/", "-", name); file = out "/" name ".patch"
                  header = 2; print > file; next }
  header > 0 { header--; if (!/\t1970-01-01 /) sub(/\t.*/, "") }
  { print > file }' "$work/all.diff"
files=$(sed -n 's#^diff -ruN a/\(.*\) b/.*#\1#p' "$work/all.diff")
echo "$(wc -l <<<"$files") patch files written to $out"

# a file that differs but gets no patch (an empty new file, a file under etc/) would be lost
if ! d=$(LC_ALL=C diff <(LC_ALL=C sort <<<"$changed") <(LC_ALL=C sort <<<"$files")); then
  echo "ERROR: the patches (>) do not cover exactly the files check_stock_diff.sh reports (<):" >&2
  echo "$d" >&2; exit 1
fi

set +e; residue=$(/usr/bin/grep -l 'locale_notes_flagged\|add_facts_flagged' "$out"/*.patch); rc=$?; set -e
(( rc == 1 )) || { echo "ERROR: residue of the timing patch (grep status $rc):" >&2; echo "$residue" >&2; exit 1; }

# sparse copy of a tree: the patched files that exist in $2 (the stock copy decides for the
# pristine tree too), fetched by `$3 <path> <dest>`; a fetch that fails aborts with its own message
sparse() {
  local dir=$1 exists_in=$2 fetch=$3 f
  for f in $files; do
    mkdir -p "$dir/$(dirname "$f")"
    if [[ -e $exists_in/$f ]]; then "$fetch" "$f" "$dir/$f"; fi
  done
}
from_stock() { cp "$stock/$1" "$2"; }
from_shared() { cp "$shared/$1" "$2"; }
from_hg() {
  (cd "$pristine_repo" && hg cat -r "tag('$tag')" "$1") > "$2" \
    || { echo "ERROR: fetching $1 at tag $tag from $pristine_repo failed" >&2; exit 1; }
}
same_trees() { LC_ALL=C diff -r "$1" "$2" >&2 || { echo "ERROR: $3" >&2; exit 1; }; }

# all patches applied in $1 (forward, or backward with -R); fuzz is never allowed; patch reports
# on stdout, which is shown on failure and returned otherwise
apply() {
  (cd "$1" && cat "$out"/*.patch | patch -p1 -F0 --no-backup-if-mismatch "${@:2}") > "$work/patch.log" \
    || { cat "$work/patch.log" >&2; echo "ERROR: patch${2:+ ${*:2}} failed on the $(basename "$1") tree" >&2; exit 1; }
  cat "$work/patch.log"
}

# round trip on the stock copy: forward = the shared tree (offset-free), backward = the stock copy
sparse "$work/stock0" "$stock" from_stock; cp -r "$work/stock0" "$work/stock"
sparse "$work/shared" "$shared" from_shared
apply "$work/stock" --dry-run > /dev/null
apply "$work/stock" > "$work/forward.log"
if /usr/bin/grep -q 'offset' "$work/forward.log"; then
  echo "ERROR: offset against the stock copy:" >&2; cat "$work/forward.log" >&2; exit 1
fi
same_trees "$work/stock" "$work/shared" "forward application does not reproduce the shared tree"
apply "$work/stock" -R > /dev/null
same_trees "$work/stock" "$work/stock0" "backward application does not reproduce the stock copy"
echo "round trip on the stock copy: ok"

# the same on the pristine checkout, where the dev patches' hunks are absent
sparse "$work/pristine0" "$stock" from_hg; cp -r "$work/pristine0" "$work/pristine"
apply "$work/pristine" > "$work/pristine.log"
/usr/bin/grep 'offset' "$work/pristine.log" || true
apply "$work/pristine" -R > /dev/null
same_trees "$work/pristine" "$work/pristine0" "backward application does not reproduce the pristine tree"
echo "round trip on the pristine tree ($pristine_repo, tag $tag): ok"

# the entries of a file's signature sections (Isabelle style: `signature NAME =` ... `end` at
# column 0), one per line as `NAME: entry`: an entry starts at a specification keyword, its
# continuation lines are joined, comments dropped, white space squeezed
entries() {
  [[ -e $1 ]] || return 0
  awk '
    function flush() {
      if (entry != "") {
        gsub(/\(\*([^*]|\*+[^*)])*\*+\)/, " ", entry); gsub(/[ \t]+/, " ", entry); sub(/^ /, "", entry); sub(/ $/, "", entry)
        print name ": " entry
      }
      entry = ""
    }
    /^signature [A-Z_0-9]+ *=/ { name = $2; inside = 1; next }
    inside && /^end;?[[:space:]]*$/ { flush(); inside = 0; next }
    !inside { next }
    { line = $0; gsub(/\(\*([^*]|\*+[^*)])*\*+\)/, " ", line); split(line, word) }
    word[1] ~ /^(val|type|eqtype|datatype|exception|structure|include|sharing)$/ { flush(); entry = $0; next }
    entry != "" { entry = entry " " $0 }' "$1"
}

# every stock entry still present unchanged; the additions, by their heads (`<path> <NAME>
# <keyword> <name>`), exactly the listed ones
: > "$work/additions"
for f in $files; do
  [[ $f == *.ML ]] || continue
  entries "$stock/$f" | LC_ALL=C sort > "$work/stock.sig"
  entries "$shared/$f" | LC_ALL=C sort > "$work/shared.sig"
  removed=$(LC_ALL=C comm -23 "$work/stock.sig" "$work/shared.sig")
  if [[ -n $removed ]]; then
    echo "ERROR: signature entries of $f changed or disappeared:" >&2; echo "$removed" >&2; exit 1
  fi
  LC_ALL=C comm -13 "$work/stock.sig" "$work/shared.sig" \
    | sed -E "s#^([A-Z_0-9]+): #$f \\1 #; s/ *(:|=| of ).*//" >> "$work/additions"
done
sed '/^[[:space:]]*\(#\|$\)/d' "$root/tools/signature_additions.txt" | LC_ALL=C sort > "$work/listed"
if ! d=$(LC_ALL=C diff "$work/listed" <(LC_ALL=C sort "$work/additions")); then
  echo "ERROR: the signature additions (>) differ from tools/signature_additions.txt (<):" >&2
  echo "$d" >&2; exit 1
fi
echo "signature sections: every stock entry unchanged, $(wc -l < "$work/additions") additions as listed"
