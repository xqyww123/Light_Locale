(* Plan section 7 test 5 (external use and propagation): the cross-command form on an HB with only an assumption and no Plain fact: all three commands succeed on the light side; a later lemma (in HB) foo then fails loudly with Duplicate fact declaration (driven through Specification.theorem_cmd). *)
theory Test5_Cross_NoPlain
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes "x = x"
consts c :: nat
light_locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all
interpretation I: HB x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_NoPlain.I." =
  ["Test5_Cross_NoPlain.I.HB_axioms", "Test5_Cross_NoPlain.I.K_axioms", "Test5_Cross_NoPlain.I.LF_axioms"]);
val _ = fails_prefix "Duplicate fact declaration"
  (fn () => lemma_in "HB" (Binding.name "foo") "[]" "x + 0 = x" simp_tac \<^theory>);
\<close>

end
