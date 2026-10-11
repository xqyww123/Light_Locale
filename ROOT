(* Light locale sessions (plan section 7).  Light_Locale_Base, Light_Locale_Test and
   Light_Locale_Test_Serial are added with their fixtures; Light_Locale_Base's parent is
   Light_Locale_Golden, so building the tests runs the golden comparison first. *)

session Light_Locale = HOL +
  description "
    Light locales: locale-style declarations whose facts live globally, for fast opening in
    AI-driven autoformalization (plan section 4).  Stubs until the Pure patch lands.
  "
  theories
    Light_Locale

session Light_Locale_Golden in "tests/Golden" = "HOL-Algebra" +
  description "
    Plan section 7 test 1 (invariance): reference output of stock Isabelle.  Run on the stock copy
    (ISABELLE_IDENTIFIER = Isabelle2025-2-stock) it records tests/golden/*.golden; run anywhere
    else it compares byte for byte.
  "
  theories
    Golden_Facts
    Golden_Transfer

session Light_Locale_Corec_Check in "tests/Corec" = "HOL-Library" +
  description "
    Plan section 7 test 1: every named fact of HOL-Corec_Examples, recorded on the stock copy and
    compared elsewhere (the wrapper reloads those theories, so they are proved by this tree's Pure).
  "
  options [quick_and_dirty]
  sessions "HOL-Corec_Examples"
  theories
    Corec_Check
