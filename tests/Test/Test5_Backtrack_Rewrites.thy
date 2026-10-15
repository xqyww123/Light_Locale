(* Plan section 7 test 5 (external use and propagation), prefix backtracking under a light edge
   with rewrites, not restated (plan section 11, implementation-period change (13)); the fixture and
   the state after interpretation I: LF t are Test5_Backtrack_Rewrites_T0.  After the upgrade
   interpretation Zp: HB t (no rewrites restated): the record is replaced (same key, Full, one
   registration with prefix Zp), I. untouched; the pre-existing syntax copy Zp.d, the theorems
   installed at activation (Zp.hbl) and the theorems backtracked afterwards (Zp.later, Zp.nd_def) are
   not rewritten.  The syntax copies of new definitions and abbreviations (nabb, nd) are HB.<name>
   applied to t in either case and never show a rewrite; a syntax declaration built from
   Morphism.term does.  These rows test the dependency-mixin claim of decision 6, not
   registration-mixin non-migration (test 10). *)
theory Test5_Backtrack_Rewrites
  imports Test5_Backtrack_Rewrites_T0
begin

interpretation Zp: HB t by unfold_locales simp
abbreviation (in HB) nabb where "nabb \<equiv> d + 1"
definition (in HB) nd where "nd = d + 1"
lemma (in HB) later: "d = d" by simp
syntax_declaration (in HB) \<open>fn phi => Proof_Context.generic_add_abbrev Print_Mode.internal
  (Morphism.binding phi \<^binding>\<open>sdd\<close>, Morphism.term phi \<^term>\<open>d + 1\<close>) #> snd\<close>

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*the record is replaced: same key, one Full record, prefix Zp*)
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
val _ = \<^assert> (null (marks_of ctxt "HB" [\<^term>\<open>t + 1\<close>]));
val _ = \<^assert> (registration_prefixes ctxt "HB" = [[("Zp", true)]]);
(*activation-time: the pre-existing syntax copy and theorem under Zp are NOT rewritten*)
val _ = \<^assert> (consts_named ctxt "d" =
  ["Test5_Backtrack_Rewrites.Zp.d", "Test5_Backtrack_Rewrites_T0.HB.d", "Test5_Backtrack_Rewrites_T0.I.d"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites.Zp.d" aconv \<^term>\<open>HB.d t\<close>);
val _ = \<^assert> (Thm.prop_of @{thm Zp.hbl} aconv \<^prop>\<open>HB.d t = HB.d t\<close>);
(*backtracking-time: the new theorem and the new definition's defining theorem are NOT rewritten*)
val _ = \<^assert> (Thm.prop_of @{thm Zp.later} aconv \<^prop>\<open>HB.d t = HB.d t\<close>);
val _ = \<^assert> (Thm.prop_of @{thm Zp.nd_def} aconv \<^prop>\<open>HB.nd t = HB.d t + 1\<close>);
(*backtracking-time: the new syntax declarations reach Zp. only, as HB.<name> applied to t*)
val _ = \<^assert> (consts_named ctxt "nabb" = ["Test5_Backtrack_Rewrites.HB.nabb", "Test5_Backtrack_Rewrites.Zp.nabb"]);
val _ = \<^assert> (consts_named ctxt "nd" = ["Test5_Backtrack_Rewrites.HB.nd", "Test5_Backtrack_Rewrites.Zp.nd"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites.Zp.nabb" aconv \<^term>\<open>HB.d t + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites.Zp.nd" aconv \<^term>\<open>HB.nd t\<close>);
(*I. is untouched*)
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_T0.I.d" aconv \<^term>\<open>t + 1\<close>);
val _ = \<^assert> (facts_under \<^theory> "Test5_Backtrack_Rewrites_T0.I." =
  ["Test5_Backtrack_Rewrites_T0.I.HB_axioms", "Test5_Backtrack_Rewrites_T0.I.LF_axioms"]);
(*the syntax copies of the Morphism.term-based declarations: sdd0 installed at activation, sdd
  backtracked after Zp -- not rewritten; I.sdd0 keeps the edge's rewrite*)
val _ = \<^assert> (consts_named ctxt "sdd0" = ["Test5_Backtrack_Rewrites.Zp.sdd0", "Test5_Backtrack_Rewrites_T0.I.sdd0"]);
val _ = \<^assert> (consts_named ctxt "sdd" = ["Test5_Backtrack_Rewrites.Zp.sdd"]);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites.Zp.sdd0" aconv \<^term>\<open>HB.d t + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites.Zp.sdd" aconv \<^term>\<open>HB.d t + 1\<close>);
val _ = \<^assert> (rhs_of ctxt "Test5_Backtrack_Rewrites_T0.I.sdd0" aconv \<^term>\<open>t + 1 + 1\<close>);
\<close>

end
