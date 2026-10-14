# Light_Locale
Light locales for Isabelle: locale-style structure declarations whose facts live globally, for fast opening in AI-driven autoformalization

## Patches to the Isabelle tree

`patches/Isabelle2025-2/*.patch` are the only record of the changes this component makes to
`contrib/Isabelle2025-2/src`: one patch per file, named by the file's path with `/` written `-`
(`src-Pure-Isar-locale.ML.patch`), generated against the stock copy `Isabelle2025-2-stock/`.
`tools/make_patches.sh [--pristine <hg repo>]` regenerates them and runs the checks: the changed
files are within `tools/patched_files.txt`, the patches round-trip on the stock copy (and on a
pristine `Isabelle2025-2` checkout when one is given), and the signature sections of the patched
ML files only gain entries.
