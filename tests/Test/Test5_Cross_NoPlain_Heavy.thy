(* Plan section 7 test 5 (external use and propagation): the heavy twin: the three commands and the later lemma (in HB) foo succeed, with exactly one I.foo. *)
theory Test5_Cross_NoPlain_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes "x = x"
consts c :: nat
locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all
interpretation I: HB x for x by unfold_locales simp_all
lemma (in HB) foo: "x + 0 = x" by simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_NoPlain_Heavy.I." =
  ["Test5_Cross_NoPlain_Heavy.I.HB_axioms", "Test5_Cross_NoPlain_Heavy.I.K_axioms",
   "Test5_Cross_NoPlain_Heavy.I.LF_axioms", "Test5_Cross_NoPlain_Heavy.I.foo"]);
\<close>

end
