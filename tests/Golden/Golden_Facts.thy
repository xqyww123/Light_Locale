(* Plan section 7 test 1: every named fact of HOL-Algebra (statement digest, premises, tags), and
   the print_locale! output of locales that declare (structure) parameters -- the printer's
   tripwire.  The imports are the session's top theories (HOL/ROOT:438-466), so that every
   HOL-Algebra theory is an ancestor. *)
theory Golden_Facts
  imports
    "HOL-Algebra.Galois_Connection" "HOL-Algebra.FiniteProduct" "HOL-Algebra.Sylow"
    "HOL-Algebra.Bij" "HOL-Algebra.Multiplicative_Group" "HOL-Algebra.Zassenhaus"
    "HOL-Algebra.Divisibility" "HOL-Algebra.IntRing" "HOL-Algebra.UnivPoly"
    "HOL-Algebra.Algebraic_Closure_Type" "HOL-Algebra.Algebra"
begin

ML_file "golden.ML"

ML \<open>
Golden.check \<^theory> "hol_algebra_facts.golden" (Golden.facts_dump \<^theory> "HOL-Algebra.");
Golden.check \<^theory> "locales.golden"
  (Golden.locales_dump \<^theory>
    ["Group.monoid", "Group.comm_group", "Ring.abelian_monoid", "Ring.ring", "UnivPoly.UP_pre_univ_prop"]);
\<close>

end
