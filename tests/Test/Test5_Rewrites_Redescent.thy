(* Plan section 7 test 5 (external use and propagation): the morphism of the upgrade's re-descent: the light edge's rewrites left-hand side f G occurs in the instantiation of B's dependency C, not in B's own; with the light import first (H = LF G S + B G for G S) the theory-level interpretation registers C s (Full) and no C (f a), with no Duplicate fact declaration. *)
theory Test5_Rewrites_Redescent
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts f :: "nat \<Rightarrow> nat set"  a :: nat  s :: "nat set"
axiomatization where fa: "f a = s"
locale C = fixes v :: "nat set" assumes "v = v"
lemma (in C) cc: "v \<union> v = v" by simp
locale B = C "f G" for G :: nat
light_locale LF = fixes G :: nat and S :: "nat set" assumes fs: "f G = S"
sublocale LF \<subseteq> B G rewrites "f G = S" by unfold_locales (simp_all add: LF.fs[OF LF_axioms])
locale H = LF G S + B G for G S
interpretation I: H a s by unfold_locales (simp_all add: fa)

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Rewrites_Redescent.I." =
  ["Test5_Rewrites_Redescent.I.B_axioms", "Test5_Rewrites_Redescent.I.C_axioms", "Test5_Rewrites_Redescent.I.H_axioms",
   "Test5_Rewrites_Redescent.I.LF_axioms", "Test5_Rewrites_Redescent.I.cc"]);
val _ = \<^assert> (marks_of ctxt "C" [\<^term>\<open>s\<close>] = [([\<^term>\<open>s\<close>], Locale.Full, [])]);
val _ = \<^assert> (null (marks_of ctxt "C" [\<^term>\<open>f a\<close>]));
val _ = \<^assert> (marks_of ctxt "B" [\<^term>\<open>a\<close>] = [([\<^term>\<open>a\<close>], Locale.Full, [])]);
val _ = \<^assert> (Thm.prop_of @{thm I.cc} aconv \<^prop>\<open>s \<union> s = s\<close>);
\<close>

end
