(* Plan section 7 test 5 (external use and propagation), the qualified variant of the
   inclusion-matching pair (plan lines 4102-4103 and 4119, the control that succeeds on both sides):
   locale H = LF a + B: K for a, interpretation I: H x for x succeeds; the special instance HB c
   is installed under I.B. (I.B.hb on c, I.B.HB_axioms), the general one reached through the light
   edge stays syntax-only under I. (I.HB_axioms: HB ?x, no general I.hb); the restocking
   definition (in HB) d then reaches I.B.d. *)
theory Test5_Inclusion_Pair_Q
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat
light_locale LF = HB
locale K = HB c
locale H = LF a + B: K for a

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Inclusion_Pair_Q.I." =
  ["Test5_Inclusion_Pair_Q.I.B.HB_axioms", "Test5_Inclusion_Pair_Q.I.B.K_axioms", "Test5_Inclusion_Pair_Q.I.B.hb",
   "Test5_Inclusion_Pair_Q.I.HB_axioms", "Test5_Inclusion_Pair_Q.I.H_axioms", "Test5_Inclusion_Pair_Q.I.LF_axioms"]);
val _ = \<^assert> (Thm.prop_of @{thm I.HB_axioms} aconv Logic.varify_global \<^prop>\<open>HB x\<close>);
val _ = \<^assert> (Thm.prop_of @{thm I.B.hb} aconv \<^prop>\<open>c = c\<close>);
\<close>

definition (in HB) d where "d = x"

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" =
  ["Test5_Inclusion_Pair_Q.HB.d", "Test5_Inclusion_Pair_Q.I.B.d", "Test5_Inclusion_Pair_Q.I.d"]);
\<close>

end
