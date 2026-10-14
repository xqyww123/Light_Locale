(* Plan section 7 test 4 (upgrade), theory-level group (d), the reversed order: I: HB t first
   (full, the heavy path), then I: LF t, whose arrival at HB t is filtered -- exactly one
   I.HB_axioms, without [simp, intro!] (the goal HB t that simp closes in group (a) is not closed
   here), HB's syntax and theorems present. *)
theory Test4_D
  imports Test4_Fixture
begin

light_locale LF = HB

interpretation I: HB t by unfold_locales simp

ML \<open>val after1 = Test_Support.facts_under \<^theory> "Test4_D.I."\<close>

interpretation I: LF t by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (after1 = ["Test4_D.I.HB_axioms", "Test4_D.I.hb", "Test4_D.I.hb2"]);
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_D.I." = sort_strings ("Test4_D.I.LF_axioms" :: after1));
val _ = \<^assert> (Test_Support.consts_named ctxt "hba" = ["Test4_D.I.hba", "Test4_Fixture.HB.hba"]);
fun by_simp prop =
  can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => simp_tac context 1)) ();
val _ = \<^assert> (not (by_simp \<^prop>\<open>HB t\<close>));
(*the light predicate fact of the same command is a simp rule*)
val _ = \<^assert> (by_simp \<^prop>\<open>LF t\<close>);
\<close>

end
