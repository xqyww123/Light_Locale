# Light_Locale
Light locales for Isabelle: locale-style structure declarations whose facts live globally, for fast opening in AI-driven autoformalization

## Patches to the Isabelle tree

`patches/Isabelle2025-2/*.patch` are the only record of the changes this component makes to
`contrib/Isabelle2025-2/src`: one patch per file, named by the file's path with `/` written `-`
(`src-Pure-Isar-locale.ML.patch`), generated against the pristine `Isabelle2025-2` sources (a
sparse checkout of the local hg clone the plan names, unless `--pristine` gives another).  The
stock copy `Isabelle2025-2-stock/` equals those sources except where the shared tree's dev
patches apply; for such a file (dev patch `show_types_nv`: currently `attrib.ML` and
`syntax_phases.ML`) the light patch is taken from the shared tree's file with the dev patch's
lines reversed, so that it applies to the pristine file and the dev patch is regenerated on top
of it (the dev patches' conda package depends on light locale).  `tools/make_patches.sh
[--pristine <hg repo>]` regenerates them and runs the checks: the patched files are exactly the
ones `tools/check_stock_diff.sh` reports (hence within `tools/patched_files.txt`), the patches
round-trip on the sparse pristine checkout, every dev patch has the same content below and above
light (which proves the reversal removed exactly the dev patch), and the signature sections of the
patched ML files keep every stock entry unchanged and gain exactly the entries whose heads (path,
signature, keyword, name; not the type) are listed in `tools/signature_additions.txt`.  The dev
patches regenerated on top of light are written under `$TMPDIR` (never here) for their package;
applying them to pristine + light gives the shared tree by construction.
