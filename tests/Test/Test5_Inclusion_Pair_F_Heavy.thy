(* The heavy twin of Test5_Inclusion_Pair_F (plan lines 4104-4107, "heavy twin the same"): locale
   LFh = HB in place of the light LF, K = HB "f c"; the restocking rows give the same single Ih.d,
   Ih.hba, Ih.C_axioms. *)
theory Test5_Inclusion_Pair_F_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  f :: "nat \<Rightarrow> nat"
locale LFh = HB
locale K = HB "f c"
locale Hh = LFh a + K for a

interpretation Ih: Hh x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm Ih.HB_axioms} aconv Logic.varify_global \<^prop>\<open>HB x\<close>);
val _ = \<^assert> (Thm.prop_of @{thm Ih.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
(*the fixture pin: the pruned special instance f c is invisible to the assertions above*)
val _ = \<^assert> (eq_list (op aconv) (instances \<^theory> "HB" (loc \<^theory> "K"), [\<^term>\<open>f c\<close>]));
\<close>

definition (in HB) d where "d = x"
abbreviation (in HB) hba where "hba \<equiv> x + 1"
locale C = HB + assumes hc: "x = x"
sublocale HB \<subseteq> C by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (consts_named ctxt "d" = ["Test5_Inclusion_Pair_F_Heavy.HB.d", "Test5_Inclusion_Pair_F_Heavy.Ih.d"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Inclusion_Pair_F_Heavy.HB.hba", "Test5_Inclusion_Pair_F_Heavy.Ih.hba"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair_F_Heavy.Ih." =
  ["Test5_Inclusion_Pair_F_Heavy.Ih.C_axioms", "Test5_Inclusion_Pair_F_Heavy.Ih.HB_axioms",
   "Test5_Inclusion_Pair_F_Heavy.Ih.Hh_axioms", "Test5_Inclusion_Pair_F_Heavy.Ih.K_axioms",
   "Test5_Inclusion_Pair_F_Heavy.Ih.LFh_axioms",
   "Test5_Inclusion_Pair_F_Heavy.Ih.d_def", "Test5_Inclusion_Pair_F_Heavy.Ih.hb", "Test5_Inclusion_Pair_F_Heavy.Ih.hc"]);
\<close>

end
