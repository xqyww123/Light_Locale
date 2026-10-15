(* The shared prefix of the two prefix-backtracking leaves under a light edge with rewrites
   (Test5_Backtrack_Rewrites: not restated; Test5_Backtrack_Rewrites_Restated: restated on the
   upgrade command; plan section 11, implementation-period change (13)).  The fixture: HB has a
   definition d before the edge; the light edge sublocale LF <= HB y rewrites "HB.d y = y + 1" has a
   left-hand side that is not a subterm of HB's instance, so interpretation I: LF t and the upgrade
   interpretation Zp: HB t land on the same key HB t (a rewrite of the instance term itself keys the
   record by the rewritten instance, as in stock).  After I: the record is Syntax_only under I, one
   registration with prefix I, and the light edge's dependency mixin rewrote the pre-existing syntax
   copy (I.d == t + 1) and the Morphism.term-based syntax declaration sdd0 (I.sdd0 == t + 1 + 1).
   The two leaves import this theory, so that their controlled comparison -- the same prefix, one
   Zp command differing -- cannot drift. *)
theory Test5_Backtrack_Rewrites_T0
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts t :: nat  f :: "nat \<Rightarrow> nat"
axiomatization where ft: "f t = t + 1"
locale HB = fixes x :: nat assumes hb: "x = x"
definition (in HB) d where "d = f x"
lemma (in HB) hbl: "d = d" by simp
light_locale LF = fixes y :: nat assumes lff: "f y = y + 1"
sublocale LF \<subseteq> HB y rewrites "HB.d y = y + 1"
  by unfold_locales (simp_all add: HB.d_def HB_def LF.lff[OF LF_axioms])
interpretation I: LF t by unfold_locales (rule ft)
(*a syntax declaration whose copy is the image of d + 1: the light edge's mixin rewrites it under I*)
syntax_declaration (in HB) \<open>fn phi => Proof_Context.generic_add_abbrev Print_Mode.internal
  (Morphism.binding phi \<^binding>\<open>sdd0\<close>, Morphism.term phi \<^term>\<open>d + 1\<close>) #> snd\<close>

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*the key is the unrewritten instance t; the record is Syntax_only with prefix I*)
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Syntax_only, ["I.x"])]);
val _ = \<^assert> (null (marks_of ctxt "HB" [\<^term>\<open>t + 1\<close>]));
val _ = \<^assert> (null (marks_of ctxt "HB" [\<^term>\<open>f t\<close>]));
val _ = \<^assert> (registration_prefixes ctxt "HB" = [[("I", true)]]);
(*positive witness: the light edge's dependency mixin rewrote the pre-existing syntax copy*)
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_T0.I.d" aconv \<^term>\<open>t + 1\<close>);
val _ = \<^assert> (facts_under \<^theory> "Test5_Backtrack_Rewrites_T0.I." =
  ["Test5_Backtrack_Rewrites_T0.I.HB_axioms", "Test5_Backtrack_Rewrites_T0.I.LF_axioms"]);
val _ = \<^assert> (consts_named ctxt "sdd0" = ["Test5_Backtrack_Rewrites_T0.I.sdd0"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_T0.I.sdd0" aconv \<^term>\<open>t + 1 + 1\<close>);
\<close>

end
