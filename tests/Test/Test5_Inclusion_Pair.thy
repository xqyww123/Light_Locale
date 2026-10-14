(* Plan section 7 test 5 (external use and propagation), the inclusion-matching pair with the
   general instance first, K = HB c: interpretation I: H x for x succeeds, exactly one
   I.HB_axioms whose statement is HB ?x, I.hb present and the instance on c.  Restocking
   afterwards: definition (in HB), abbreviation (in HB) and the sublocale HB <= C each reach I.
   exactly once (I.d, I.hba, I.C_axioms). *)
theory Test5_Inclusion_Pair
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  f :: "nat \<Rightarrow> nat"
light_locale LF = HB
locale K = HB c
locale H = LF a + K for a

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair.I." =
  ["Test5_Inclusion_Pair.I.HB_axioms", "Test5_Inclusion_Pair.I.H_axioms", "Test5_Inclusion_Pair.I.K_axioms",
   "Test5_Inclusion_Pair.I.LF_axioms", "Test5_Inclusion_Pair.I.hb"]);
val _ = \<^assert> (Thm.prop_of @{thm I.HB_axioms} aconv Logic.varify_global \<^prop>\<open>HB x\<close>);
val _ = \<^assert> (Thm.prop_of @{thm I.hb} aconv \<^prop>\<open>c = c\<close>);
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>c\<close>] =
  [([\<^term>\<open>c\<close>], Locale.Full, []), ([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Syntax_only, ["I.x"])]);
\<close>

definition (in HB) d where "d = x"
abbreviation (in HB) hba where "hba \<equiv> x + 1"

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (consts_named ctxt "d" = ["Test5_Inclusion_Pair.HB.d", "Test5_Inclusion_Pair.I.d"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Inclusion_Pair.HB.hba", "Test5_Inclusion_Pair.I.hba"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair.I.d" = ["Test5_Inclusion_Pair.I.d_def"]);
\<close>

locale C = HB + assumes hc: "x = x"
sublocale HB \<subseteq> C by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair.I." =
  ["Test5_Inclusion_Pair.I.C_axioms", "Test5_Inclusion_Pair.I.HB_axioms", "Test5_Inclusion_Pair.I.H_axioms", "Test5_Inclusion_Pair.I.K_axioms",
   "Test5_Inclusion_Pair.I.LF_axioms", "Test5_Inclusion_Pair.I.d_def", "Test5_Inclusion_Pair.I.hb", "Test5_Inclusion_Pair.I.hc"]);
\<close>

end
