#!/usr/bin/env bash
# Plan §8 step 5.  The files under patches/Isabelle2025-2/ are the only record of light locale's
# changes to the Isabelle tree: one `diff -ruN` of a sparse pristine tree against a sparse
# "pristine + light" tree, split per file (file name = the path with `/` written `-`), header
# timestamps dropped except the epoch one that marks a new file (patch creates and removes the
# file by it).  The pristine tree is the tag's checkout (= the stock copy wherever no dev patch
# touches the file; the stock copy carries the dev patches of the shared tree).  Where a dev patch
# touches a file (plan §11 (6) D1 and (32): show_types_nv, currently attrib.ML with one added
# line and syntax_phases.ML), "pristine + light" is the shared tree's file with the dev patch's
# lines reversed one by one (each must occur exactly once there), so that the light patch applies
# to pristine and the dev patch is regenerated on top of it (the conda package qiyuan_dev_patches
# depends on light locale).  Then the checks of that step: the patched files are exactly the
# files check_stock_diff.sh reports (hence within tools/patched_files.txt), no residue of the
# timing patch, a round trip on the sparse pristine checkout (forward reproduces "pristine +
# light" byte for byte, no offset, no fuzz; backward the pristine tree; new files created and
# removed), the dev patches' content is the same below and above light (the hunk bodies of
# pristine->stock and of "pristine + light"->shared agree -- the check that the reversal removed
# exactly the dev patch), and the signature sections of every patched .ML file keep every stock
# entry unchanged and gain exactly the entries whose heads (path, signature, keyword, name; not
# the type) are listed in tools/signature_additions.txt.  The regenerated dev patches are a
# by-product for qiyuan_dev_patches, written under $TMPDIR, never into this repository; applying
# them on "pristine + light" and comparing with the shared tree is a sanity identity (they are
# the diff of those two trees), not a further check.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
shared=$root/../Isabelle2025-2
stock=$root/Isabelle2025-2-stock
out=$root/patches/Isabelle2025-2
tag=$(basename "$out")
devout=${TMPDIR:-/tmp}/light_locale_dev_patches
usage() { echo "usage: $0 [--pristine <hg repo>]" >&2; exit 2; }
case $#:${1:-} in
  0:) pristine_repo=$HOME/isa_release_proto/isabelle-src ;;
  2:--pristine) pristine_repo=$2 ;;
  *) usage ;;
esac
[[ -n $pristine_repo ]] || usage
hg -R "$pristine_repo" id -r "tag('$tag')" > /dev/null \
  || { echo "ERROR: $pristine_repo is not an hg repository with tag $tag" >&2; exit 1; }

files=$("$root/tools/check_stock_diff.sh" | sed -n 's/^changed  //p')

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT

from_hg() {
  (cd "$pristine_repo" && hg cat -r "tag('$tag')" "$1") > "$2" \
    || { echo "ERROR: fetching $1 at tag $tag from $pristine_repo failed" >&2; exit 1; }
}

# the shared tree's file with the dev patch's lines reversed: the hunks of pristine->stock (the
# two diff header lines skipped), each `+` line paired with the `-` line at the same place of its
# hunk (replaced) or, in a hunk that only adds, deleted; a hunk that removes more than it adds
# cannot be reversed by lines, and a hunk that both replaces and adds is not examined for
# reversibility (which `+` line is the insertion may be ambiguous) -- both abort; every `+` line
# must occur exactly once in the shared tree's file
reverse_dev() {
  { LC_ALL=C diff -U0 "$1" "$2" || (( $? == 1 )); } | awk -v shared="$3" '
    function fail(msg) { print "ERROR: " msg > "/dev/stderr"; failed = 1; exit 1 }
    function flush(  i) {
      if (nminus > nplus) fail("a dev hunk of " shared " removes more lines than it adds")
      if (nminus > 0 && nplus > nminus) fail("a dev hunk of " shared " both replaces and adds lines")
      for (i = 0; i < nplus; i++) { repl[plus[i]] = (i < nminus) ? minus[i] : "\001DELETE"; seen[plus[i]] = 0 }
      nminus = nplus = 0
    }
    NR <= 2 { next }
    /^@@/ { flush(); next }
    /^-/ { minus[nminus++] = substr($0, 2); next }
    /^\+/ { plus[nplus++] = substr($0, 2); next }
    END {
      if (failed) exit 1
      flush()
      if (failed) exit 1
      while ((getline line < shared) > 0) {
        if (line in repl) { seen[line]++; if (repl[line] != "\001DELETE") print repl[line] }
        else print line
      }
      for (l in repl) if (seen[l] != 1) fail("dev line not found exactly once in " shared ": " l)
    }'
}

# the three sparse trees: pristine (the files that exist in the stock copy), light = pristine +
# light's changes, shared; the dev files are those where the stock copy differs from pristine
dev_files=
for f in $files; do
  mkdir -p "$work/pristine0/$(dirname "$f")" "$work/light/$(dirname "$f")" "$work/shared/$(dirname "$f")"
  [[ -e $shared/$f ]] && cp "$shared/$f" "$work/shared/$f"
  if [[ -e $stock/$f ]]; then
    from_hg "$f" "$work/pristine0/$f"
    if LC_ALL=C cmp -s "$work/pristine0/$f" "$stock/$f"; then
      cp "$shared/$f" "$work/light/$f"
    else
      dev_files="$dev_files $f"
      reverse_dev "$work/pristine0/$f" "$stock/$f" "$shared/$f" > "$work/light/$f" \
        || { echo "ERROR: the dev patch of $f cannot be reversed on the shared tree" >&2; exit 1; }
      # awk ends every line; a file without a final newline (attrib.ML) keeps it that way
      [[ -n $(tail -c1 "$shared/$f") ]] && truncate -s -1 "$work/light/$f"
    fi
  elif [[ -e $shared/$f ]]; then
    cp "$shared/$f" "$work/light/$f"
  fi
done

ln -s "$work/pristine0" "$work/a"; ln -s "$work/light" "$work/b"
set +e; (cd "$work" && TZ=UTC LC_ALL=C diff -ruN a b > all.diff); rc=$?; set -e
[[ $rc == 1 ]] || { echo "ERROR: diff exit $rc (0 = no difference at all)" >&2; exit 1; }

# the two header lines after each `diff` line lose their timestamps; hunk body lines are left alone
mkdir -p "$out"; rm -f "$out"/*.patch
awk -v out="$out" '
  /^diff -ruN / { name = $3; sub(/^a\//, "", name); gsub("/", "-", name); file = out "/" name ".patch"
                  header = 2; print > file; next }
  header > 0 { header--; if (!/\t1970-01-01 /) sub(/\t.*/, "") }
  { print > file }' "$work/all.diff"
patched=$(sed -n 's#^diff -ruN a/\(.*\) b/.*#\1#p' "$work/all.diff")
echo "$(wc -l <<<"$patched") patch files written to $out"

# a file that differs but gets no patch (an empty new file, a file under etc/) would be lost
if ! d=$(LC_ALL=C diff <(LC_ALL=C sort <<<"$files") <(LC_ALL=C sort <<<"$patched")); then
  echo "ERROR: the patches (>) do not cover exactly the files check_stock_diff.sh reports (<):" >&2
  echo "$d" >&2; exit 1
fi

set +e; residue=$(/usr/bin/grep -l 'locale_notes_flagged\|add_facts_flagged' "$out"/*.patch); rc=$?; set -e
(( rc == 1 )) || { echo "ERROR: residue of the timing patch (grep status $rc):" >&2; echo "$residue" >&2; exit 1; }

same_trees() { LC_ALL=C diff -r "$1" "$2" >&2 || { echo "ERROR: $3" >&2; exit 1; }; }

# all patches applied in $1 (forward, or backward with -R); fuzz is never allowed; patch reports
# on stdout, which is shown on failure and returned otherwise
apply() {
  (cd "$1" && cat "$out"/*.patch | patch -p1 -F0 --no-backup-if-mismatch "${@:2}") > "$work/patch.log" \
    || { cat "$work/patch.log" >&2; echo "ERROR: patch${2:+ ${*:2}} failed on the $(basename "$1") tree" >&2; exit 1; }
  cat "$work/patch.log"
}

# round trip on the pristine checkout: forward = pristine + light (offset-free), backward = pristine
cp -r "$work/pristine0" "$work/pristine"
apply "$work/pristine" --dry-run > /dev/null
apply "$work/pristine" > "$work/forward.log"
if /usr/bin/grep -q 'offset' "$work/forward.log"; then
  echo "ERROR: offset against the pristine tree:" >&2; cat "$work/forward.log" >&2; exit 1
fi
same_trees "$work/pristine" "$work/light" "forward application does not reproduce pristine + light"
apply "$work/pristine" -R > /dev/null
same_trees "$work/pristine" "$work/pristine0" "backward application does not reproduce the pristine tree"
echo "round trip on the pristine tree ($pristine_repo, tag $tag): ok"

# the dev patches: the same content below and above light (the hunk bodies, diff's two header
# lines skipped); then they are regenerated on top of light, and applying them there gives the
# shared tree by construction (a sanity identity, see the header)
hunk_bodies() {
  { LC_ALL=C diff -U0 "$1" "$2" || (( $? == 1 )); } | sed '1,2d' | /usr/bin/grep '^[-+]'
}
rm -rf "$devout"; mkdir -p "$devout"
cp -r "$work/light" "$work/installed"
for f in $dev_files; do
  if ! d=$(LC_ALL=C diff <(hunk_bodies "$work/pristine0/$f" "$stock/$f") <(hunk_bodies "$work/light/$f" "$shared/$f")); then
    echo "ERROR: the dev patch of $f changes between pristine->stock (<) and light->shared (>):" >&2
    echo "$d" >&2; exit 1
  fi
  name=$(sed 's#/#-#g' <<<"$f").patch
  { (cd "$work" && TZ=UTC LC_ALL=C diff -u "light/$f" "shared/$f") || (( $? == 1 )); } | sed '1,2s/\t.*//' > "$devout/$name"
  (cd "$work/installed" && patch -p1 -F0 --no-backup-if-mismatch "$f" < "$devout/$name") > /dev/null \
    || { echo "ERROR: the regenerated dev patch of $f does not apply on pristine + light" >&2; exit 1; }
done
same_trees "$work/installed" "$work/shared" "pristine + light + the regenerated dev patches do not reproduce the shared tree (identity broken)"
if [[ -n $dev_files ]]; then
  echo "dev patches: same content below and above light, regenerated on top of light:$dev_files -> $devout"
else
  rmdir "$devout"; echo "no file carries a dev patch"
fi

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
