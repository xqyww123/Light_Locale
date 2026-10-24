# Light_Locale
Light locales for Isabelle: locale-style structure declarations whose facts live globally, for fast opening in AI-driven autoformalization

## Patches to the Isabelle tree

`patches/Isabelle2025-2/*.patch` are the only record of the changes this component makes to
the Isabelle sources: one patch per file, named by the file's path with `/` written `-`
(`src-Pure-Isar-locale.ML.patch`), beside `provenance.txt`.  They are generated from the
Isabelle source repository (`contrib/Isabelle2025-2` and its worktrees; the rules are the
section "Working in the Isabelle source repository" of `contrib/my_better_isabelle_prover/README.md`):
development happens in the private tree `contrib/Isabelle2025-2-light_locale` on branch
`Isabelle2025-2/light_locale`, every Isabelle run there goes through `run-tree`, and a release
is `make-patches --package contrib/light_locale Isabelle2025-2/light_locale <version>`, run on
the owner's order.  Its gates read three files here: `tools/patched_files.txt` (the files
changed since the base release tag must be exactly these), `tools/signature_additions.txt` (the
signature sections of the patched ML files keep every stock entry and gain exactly the entries
whose heads -- path, signature, keyword, name; not the type -- are listed) and
`tools/required_sessions.txt` (the tested records `run-tree` writes on the released commit
must cover these sessions).  The golden files of plan section 7 test 1 are recorded on light's
stock tree `contrib/Isabelle2025-2-light_locale-stock` (the tree without light) and compared on
every other tree; `tools/record_golden_metadata.sh` writes `tests/golden/METADATA` after a
recording.
