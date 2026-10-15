(* The heavy twin of Test5_Inclusion_Pair_Q (plan lines 4102-4103 and 4119: the qualified variant succeeds on
   both sides): locale LFh = HB in place of the light LF.  The general instance HB ?x arrives first
   and Full, so the qualified special instance B: K is pruned: Ih.hb is the general theorem, nothing
   of HB is installed under Ih.B., and definition (in HB) d reaches Ih.d only. *)
theory Test5_Inclusion_Pair_Q_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat
locale LFh = HB
locale K = HB c
locale Hh = LFh a + B: K for a

interpretation Ih: Hh x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair_Q_Heavy.Ih." =
  ["Test5_Inclusion_Pair_Q_Heavy.Ih.B.K_axioms", "Test5_Inclusion_Pair_Q_Heavy.Ih.HB_axioms",
   "Test5_Inclusion_Pair_Q_Heavy.Ih.Hh_axioms", "Test5_Inclusion_Pair_Q_Heavy.Ih.LFh_axioms",
   "Test5_Inclusion_Pair_Q_Heavy.Ih.hb"]);
val _ = \<^assert> (Thm.prop_of @{thm Ih.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
\<close>

definition (in HB) d where "d = x"

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" =
  ["Test5_Inclusion_Pair_Q_Heavy.HB.d", "Test5_Inclusion_Pair_Q_Heavy.Ih.d"]);
\<close>

end
