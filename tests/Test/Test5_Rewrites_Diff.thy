(* Plan section 7 test 5 (external use and propagation): the differential: after sublocale LF <= B t rewrites eq, whose left-hand side occurs neither in t nor in any import term of B, the same-qualifier interpretation I: B t' raises no Duplicate fact declaration. *)
theory Test5_Rewrites_Diff
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat
light_locale LF = HB
locale B = fixes u :: nat assumes bu: "u = u"
lemma (in B) bb: "u + 0 = u" by simp
sublocale LF \<subseteq> B "x + 1" rewrites "x + 1 + 0 = x + 1" by unfold_locales simp_all

interpretation I: LF c by unfold_locales simp

ML \<open>
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "B" [\<^term>\<open>c + 1\<close>] =
  [([\<^term>\<open>c + 1\<close>], Locale.Syntax_only, ["I.x"])]);
\<close>

interpretation I: B "c + 1" by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Rewrites_Diff.I." =
  ["Test5_Rewrites_Diff.I.B_axioms", "Test5_Rewrites_Diff.I.HB_axioms", "Test5_Rewrites_Diff.I.LF_axioms",
   "Test5_Rewrites_Diff.I.bb", "Test5_Rewrites_Diff.I.bu"]);
\<close>

end
