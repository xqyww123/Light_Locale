(* Plan section 7 test 5 (external use and propagation): sublocale LF <= B2 s and an interpretation
   of LF, the edge after the interpretation (the fixture is Test5_Propagation_T0): both orders give
   the same result -- B2 (t + 1) syntax-only under J, no theorem of B2 under J. *)
theory Test5_Propagation_B2_After
  imports Test5_Propagation_T0
begin

ML \<open>open Test_Support\<close>

locale H = LF

locale B2 = fixes w :: nat assumes "w = w"
lemma (in B2) b2l: "w + 0 = w" by simp
interpretation J: LF t by unfold_locales simp
sublocale LF \<subseteq> B2 "z + 1" by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_B2_After.J." =
  ["Test5_Propagation_B2_After.J.B2_axioms", "Test5_Propagation_B2_After.J.LF_axioms", "Test5_Propagation_B2_After.J.T_axioms"]);
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "B2" [\<^term>\<open>t + 1\<close>] = [([\<^term>\<open>t + 1\<close>], Locale.Syntax_only, ["J.x"])]);
\<close>

end
