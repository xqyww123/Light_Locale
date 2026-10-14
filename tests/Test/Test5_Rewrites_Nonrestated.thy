(* Plan section 7 test 5 (external use and propagation): not restated, the left-hand side occurs in a dependency's import term.  locale B = C "f G" for G, sublocale LF <= B G rewrites "f G = S": after the theory-level interpretation I: LF a s the non-restated interpretation I: B a fails on the light side (the upgrade re-descends with the rewriting morphism to C s while the plain arrival registers C (f a)); the restated variant succeeds with exactly one I.C_axioms. *)
theory Test5_Rewrites_Nonrestated
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

interpretation I: LF a s by unfold_locales (rule fa)

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Rewrites_Nonrestated.I." =
  ["Test5_Rewrites_Nonrestated.I.B_axioms", "Test5_Rewrites_Nonrestated.I.C_axioms", "Test5_Rewrites_Nonrestated.I.LF_axioms"]);
val _ = \<^assert> (marks_of ctxt "C" [\<^term>\<open>s\<close>] = [([\<^term>\<open>s\<close>], Locale.Syntax_only, ["I.x"])]);
val _ = \<^assert> (null (marks_of ctxt "C" [\<^term>\<open>f a\<close>]));
val _ = \<^assert>
  ((interpretation_cmd "I: B a" \<^theory>; false)
    handle ERROR msg => String.isPrefix "Duplicate fact declaration" (XML.content_of (YXML.parse_body msg)));
\<close>

interpretation I: B a rewrites "f a = s" by unfold_locales (simp_all add: fa)

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Rewrites_Nonrestated.I." =
  ["Test5_Rewrites_Nonrestated.I.B_axioms", "Test5_Rewrites_Nonrestated.I.C_axioms",
   "Test5_Rewrites_Nonrestated.I.LF_axioms", "Test5_Rewrites_Nonrestated.I.cc"]);
val _ = \<^assert> (marks_of ctxt "C" [\<^term>\<open>s\<close>] = [([\<^term>\<open>s\<close>], Locale.Full, [])]);
val _ = \<^assert> (null (marks_of ctxt "C" [\<^term>\<open>f a\<close>]));
\<close>

end
