(* Plan section 7 test 5 (external use and propagation): a syntax-only record and a full record side by side: interpretation I: LF t1 and interpretation Zp: HB t2 (two ground instances); a later lemma (in HB) later reaches Zp. but not I. (Plain polarity), a later abbreviation (in HB) reaches both (Syntax_copy polarity); interpretation I: HB t1 then raises no Duplicate fact declaration and gives exactly one I.later. *)
theory Test5_Coexist
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts t1 :: nat  t2 :: nat
light_locale LF = HB
interpretation I: LF t1 by unfold_locales simp
interpretation Zp: HB t2 by unfold_locales simp
lemma (in HB) later: "x + 0 = x" by simp
abbreviation (in HB) newabbrev where "newabbrev \<equiv> x + 1"

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Coexist.I." = ["Test5_Coexist.I.HB_axioms", "Test5_Coexist.I.LF_axioms"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Coexist.Zp." = ["Test5_Coexist.Zp.HB_axioms", "Test5_Coexist.Zp.hb", "Test5_Coexist.Zp.later"]);
val _ = \<^assert> (consts_named ctxt "newabbrev" = ["Test5_Coexist.HB.newabbrev", "Test5_Coexist.I.newabbrev", "Test5_Coexist.Zp.newabbrev"]);
\<close>

interpretation I: HB t1 by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Coexist.I." =
  ["Test5_Coexist.I.HB_axioms", "Test5_Coexist.I.LF_axioms", "Test5_Coexist.I.hb", "Test5_Coexist.I.later"]);
\<close>

end
