(* Plan section 7 test 5 (external use and propagation), prefix backtracking under a light edge
   with rewrites, restated on the upgrade command (plan section 11, implementation-period change (13)).  The fixture: HB has a
   definition d before the edge; the light edge sublocale LF <= HB y rewrites "HB.d y = y + 1" has a
   left-hand side that is not a subterm of HB's instance, so interpretation I: LF t and the upgrade
   interpretation Zp: HB t land on the same key HB t (a rewrite of the instance term itself keys the
   record by the rewritten instance, as in stock).  After I: the record is Syntax_only under I, one
   registration with prefix I, and the light edge's dependency mixin rewrote the pre-existing syntax
   copy (I.d == t + 1).  After Zp: the record is replaced (same key, Full, one registration with
   prefix Zp), I. untouched; the pre-existing syntax copy Zp.d, the theorems installed at activation (Zp.hbl) and the theorems backtracked afterwards (Zp.later, Zp.nd_def) are rewritten.  The syntax copies of new definitions and abbreviations (nabb, nd) are HB.<name> applied to t
   in either case and never show a rewrite; a syntax declaration built from Morphism.term does.  These rows test the dependency-mixin claim of decision 6, not registration-mixin
   non-migration (test 10). *)
theory Test5_Backtrack_Rewrites_Restated
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
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Syntax_only, ["I.x"])]);
val _ = \<^assert> (null (marks_of ctxt "HB" [\<^term>\<open>t + 1\<close>]));
val _ = \<^assert> (registration_prefixes ctxt "HB" = [[("I", true)]]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.I.d" aconv \<^term>\<open>t + 1\<close>);
val _ = \<^assert> (facts_under \<^theory> "Test5_Backtrack_Rewrites_Restated.I." = ["Test5_Backtrack_Rewrites_Restated.I.HB_axioms", "Test5_Backtrack_Rewrites_Restated.I.LF_axioms"]);
val _ = \<^assert> (consts_named ctxt "sdd0" = ["Test5_Backtrack_Rewrites_Restated.I.sdd0"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.I.sdd0" aconv \<^term>\<open>t + 1 + 1\<close>);
\<close>

interpretation Zp: HB t rewrites "HB.d t = t + 1" by unfold_locales (simp_all add: HB.d_def HB_def ft)
abbreviation (in HB) nabb where "nabb \<equiv> d + 1"
definition (in HB) nd where "nd = d + 1"
lemma (in HB) later: "d = d" by simp
syntax_declaration (in HB) \<open>fn phi => Proof_Context.generic_add_abbrev Print_Mode.internal
  (Morphism.binding phi \<^binding>\<open>sdd\<close>, Morphism.term phi \<^term>\<open>d + 1\<close>) #> snd\<close>

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*the record is replaced on the same key*)
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
val _ = \<^assert> (null (marks_of ctxt "HB" [\<^term>\<open>t + 1\<close>]));
val _ = \<^assert> (registration_prefixes ctxt "HB" = [[("Zp", true)]]);
(*activation-time: the pre-existing syntax copy and theorem under Zp ARE rewritten*)
val _ = \<^assert> (consts_named ctxt "d" = ["Test5_Backtrack_Rewrites_Restated.HB.d", "Test5_Backtrack_Rewrites_Restated.I.d", "Test5_Backtrack_Rewrites_Restated.Zp.d"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.Zp.d" aconv \<^term>\<open>t + 1\<close>);
val _ = \<^assert> (Thm.prop_of @{thm Zp.hbl} aconv \<^prop>\<open>t + 1 = t + 1\<close>);
(*backtracking-time: the new theorem and the new definition's defining theorem ARE rewritten*)
val _ = \<^assert> (Thm.prop_of @{thm Zp.later} aconv \<^prop>\<open>t + 1 = t + 1\<close>);
val _ = \<^assert> (Thm.prop_of @{thm Zp.nd_def} aconv \<^prop>\<open>HB.nd t = t + 1 + 1\<close>);
(*backtracking-time: the new syntax declarations are HB.<name> applied to t -- NOT rewritten, even restated*)
val _ = \<^assert> (consts_named ctxt "nabb" = ["Test5_Backtrack_Rewrites_Restated.HB.nabb", "Test5_Backtrack_Rewrites_Restated.Zp.nabb"]);
val _ = \<^assert> (consts_named ctxt "nd" = ["Test5_Backtrack_Rewrites_Restated.HB.nd", "Test5_Backtrack_Rewrites_Restated.Zp.nd"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.Zp.nabb" aconv \<^term>\<open>HB.d t + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.Zp.nd" aconv \<^term>\<open>HB.nd t\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.I.d" aconv \<^term>\<open>t + 1\<close>);
val _ = \<^assert> (facts_under \<^theory> "Test5_Backtrack_Rewrites_Restated.I." = ["Test5_Backtrack_Rewrites_Restated.I.HB_axioms", "Test5_Backtrack_Rewrites_Restated.I.LF_axioms"]);
(*the syntax copies of the Morphism.term-based declarations: sdd0 installed at activation, sdd
  backtracked after Zp -- rewritten; I.sdd0 keeps the edge's rewrite*)
val _ = \<^assert> (consts_named ctxt "sdd0" = ["Test5_Backtrack_Rewrites_Restated.I.sdd0", "Test5_Backtrack_Rewrites_Restated.Zp.sdd0"]);
val _ = \<^assert> (consts_named ctxt "sdd" = ["Test5_Backtrack_Rewrites_Restated.Zp.sdd"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.Zp.sdd0" aconv \<^term>\<open>t + 1 + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.Zp.sdd" aconv \<^term>\<open>t + 1 + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_Restated.I.sdd0" aconv \<^term>\<open>t + 1 + 1\<close>);
\<close>

end
