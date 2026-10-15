(* Plan section 7 test 5 (external use and propagation), a filtered arrival absorbs no mark (Light side).
   Five commands: I: LF x for x (HB [?x, c] syntax-only under I), I: K (HB [d, c] full, selection Rest,
   installs I.hb), J: HB x z for x z ([?x, ?z] full), Q: K4 x for x (HB [?x, c] arrives Full and is
   filtered by the [?x, ?z] record: not registered, not activated), definition (in HB) dd -- exactly
   one I.dd, J.dd present; after step 4 the record of HB [?x, c] is still Syntax_only with effect I. *)
theory Test5_Filtered
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x z :: nat assumes hbx: "x = x"
lemma (in HB) hb: "x + z = z + x" by simp
consts c :: nat  d :: nat
light_locale LF = HB x c for x
locale K = HB d c
locale K4 = HB x c for x

interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered.I." =
  ["Test5_Filtered.I.HB_axioms", "Test5_Filtered.I.K_axioms", "Test5_Filtered.I.LF_axioms", "Test5_Filtered.I.hb", "Test5_Filtered.I.hbx"]);
\<close>

ML \<open>
val xc = [Var (("x", 0), \<^typ>\<open>nat\<close>), \<^term>\<open>c\<close>];
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "HB" xc = [(xc, Locale.Syntax_only, ["I.x"])]);
\<close>

interpretation J: HB x z for x z by unfold_locales simp_all
interpretation Q: K4 x for x by unfold_locales simp_all

ML \<open>
(*after step 4 the record of HB [?x, c] is still Syntax_only with effect I*)
val _ = \<^assert> (marks_are (Proof_Context.init_global \<^theory>) "HB" xc
  [([Var (("x", 0), \<^typ>\<open>nat\<close>), Var (("z", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), (xc, Locale.Syntax_only, ["I.x"])]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered.Q." = ["Test5_Filtered.Q.K4_axioms"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered.J." = ["Test5_Filtered.J.HB_axioms", "Test5_Filtered.J.hb", "Test5_Filtered.J.hbx"]);
\<close>

definition (in HB) dd where "dd = x"

ML \<open>
val _ = \<^assert> (sort_strings (consts_named (Proof_Context.init_global \<^theory>) "dd") =
  ["Test5_Filtered.HB.dd", "Test5_Filtered.I.dd", "Test5_Filtered.J.dd"]);
\<close>

end
