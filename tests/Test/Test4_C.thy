(* Plan section 7 test 4 (upgrade), theory-level group (c): three commands, new named effect,
   selection All.  I: LF t records HB t syntax-only under I; J: M t reaches HB t syntax-only again
   under J, which the filter drops (recorded level >= requested level), so J. gets neither HB's note
   nor the effect; J: HB t then installs everything under J -- exactly one J.HB_axioms, with
   witness_add, the abbreviation and the heavy theorems under J., no Duplicate fact declaration. *)
theory Test4_C
  imports Test4_Fixture
begin

light_locale LF = HB

light_locale M = HB

interpretation I: LF t by unfold_locales simp

interpretation J: M t by unfold_locales simp

ML \<open>
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_C.I." = ["Test4_C.I.HB_axioms", "Test4_C.I.LF_axioms"]);
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_C.J." = ["Test4_C.J.M_axioms"]);
val _ = \<^assert> (Test_Support.consts_named (Proof_Context.init_global \<^theory>) "hba" = ["Test4_C.I.hba", "Test4_Fixture.HB.hba"]);
\<close>

interpretation J: HB t by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_C.J." =
  ["Test4_C.J.HB_axioms", "Test4_C.J.M_axioms", "Test4_C.J.hb", "Test4_C.J.hb2"]);
val _ = \<^assert> (Test_Support.consts_named ctxt "hba" = ["Test4_C.I.hba", "Test4_C.J.hba", "Test4_Fixture.HB.hba"]);
(*witness_add: HB t is a witness of the theory context (Locale.get_witnesses)*)
val _ = \<^assert> (exists (fn th => Thm.prop_of th aconv \<^prop>\<open>HB t\<close>) (Locale.get_witnesses ctxt));
\<close>

end
