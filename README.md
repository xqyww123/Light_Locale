# Light_Locale
Light locales for Isabelle: locale-style structure declarations whose facts live globally, for fast opening in AI-driven autoformalization

## Patches to the Isabelle tree

`patches/Isabelle2025-2/*.patch` are the only record of the changes this component makes to
`contrib/Isabelle2025-2/src`: one patch per file, named by the file's path with `/` written `-`
(`src-Pure-Isar-locale.ML.patch`), generated against the stock copy `Isabelle2025-2-stock/`.
`tools/make_patches.sh [--pristine <hg repo>]` regenerates them and runs the checks: the patched
files are exactly the ones `tools/check_stock_diff.sh` reports (hence within
`tools/patched_files.txt`), the patches round-trip on a sparse copy of the stock copy and on a
sparse pristine `Isabelle2025-2` checkout (the local hg clone the plan names, unless `--pristine`
gives another), and the signature sections of the patched ML files keep every stock entry
unchanged and gain exactly the entries whose heads (path, signature, keyword, name; not the
type) are listed in `tools/signature_additions.txt`.
