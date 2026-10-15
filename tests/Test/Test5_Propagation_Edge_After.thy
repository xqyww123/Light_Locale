(* Plan section 7 test 5 (external use and propagation): an edge added to the heavy importer after
   the registration (the fixture is Test5_Propagation_T0): locale H = LF, interpretation I: H t
   (T t syntax-only), then sublocale H <= T z -- T t becomes Full and I.tt is reachable. *)
theory Test5_Propagation_Edge_After
  imports Test5_Propagation_T0
begin

ML \<open>open Test_Support\<close>

locale H = LF
interpretation I: H t by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Edge_After.I." =
  ["Test5_Propagation_Edge_After.I.H_axioms", "Test5_Propagation_Edge_After.I.LF_axioms", "Test5_Propagation_Edge_After.I.T_axioms"]);
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "T" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Syntax_only, ["I.x"])]);
\<close>

sublocale H \<subseteq> T z by unfold_locales

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Edge_After.I." =
  ["Test5_Propagation_Edge_After.I.H_axioms", "Test5_Propagation_Edge_After.I.LF_axioms",
   "Test5_Propagation_Edge_After.I.T_axioms", "Test5_Propagation_Edge_After.I.tt"]);
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "T" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
\<close>

end
