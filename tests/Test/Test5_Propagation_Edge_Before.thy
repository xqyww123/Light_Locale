(* Plan section 7 test 5 (external use and propagation): the other order: sublocale H <= T z first, then interpretation I: H t -- the same result, T t Full and I.tt reachable. *)
theory Test5_Propagation_Edge_Before
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale T = fixes z :: nat assumes "z = z"
lemma (in T) tt: "z + 0 = z" by simp
abbreviation (in T) ta where "ta \<equiv> z + 1"
consts t :: nat
light_locale LF = T
locale H = LF
sublocale H \<subseteq> T z by unfold_locales
interpretation I: H t by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Edge_Before.I." =
  ["Test5_Propagation_Edge_Before.I.H_axioms", "Test5_Propagation_Edge_Before.I.LF_axioms",
   "Test5_Propagation_Edge_Before.I.T_axioms", "Test5_Propagation_Edge_Before.I.tt"]);
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "T" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
\<close>

end
