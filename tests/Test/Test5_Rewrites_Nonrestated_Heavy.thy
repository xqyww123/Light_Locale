(* Plan section 7 test 5 (external use and propagation): the heavy twin: the non-restated interpretation I: B a succeeds (B a is already Full and is skipped). *)
theory Test5_Rewrites_Nonrestated_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts f :: "nat \<Rightarrow> nat set"  a :: nat  s :: "nat set"
axiomatization where fa: "f a = s"
locale C = fixes v :: "nat set" assumes "v = v"
lemma (in C) cc: "v \<union> v = v" by simp
locale B = C "f G" for G :: nat
locale LF = fixes G :: nat and S :: "nat set" assumes fs: "f G = S"
sublocale LF \<subseteq> B G rewrites "f G = S" by unfold_locales (simp_all add: LF.fs[OF LF_axioms])
interpretation I: LF a s by unfold_locales (rule fa)
interpretation I: B a by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Rewrites_Nonrestated_Heavy.I." =
  ["Test5_Rewrites_Nonrestated_Heavy.I.B_axioms", "Test5_Rewrites_Nonrestated_Heavy.I.C_axioms",
   "Test5_Rewrites_Nonrestated_Heavy.I.LF_axioms", "Test5_Rewrites_Nonrestated_Heavy.I.cc",
   "Test5_Rewrites_Nonrestated_Heavy.I.fs"]);
\<close>

end
