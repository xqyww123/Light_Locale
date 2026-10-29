(* Plan section 7 test 12 (repair phase, step 1), the table after a theory-level interpretation
   (batch-1 plan section 4.1, A3; "also found downstream" is the merge group's Tab_M1); in a proof
   with a second instance from interpret, instance_tac returns both facts, the newest first, and
   resolve_closing_setclass_prems keeps both alternatives (hw6 keeps the instance in the
   conclusion: EVERY in close_setclass_prems_tac drops a result equal to the one before,
   tactical.ML:133-150, so two closings of hw's LF ?S, both leaving True, give one state). *)
theory Test12_Table_Interp
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

interpretation I: LF t by (simp add: LF_def UP_cring_def t)

ML \<open>check_rows [("A3", fn () => retrieves_only \<^context> \<^prop>\<open>LF t\<close> @{thm I.LF_axioms})]\<close>

lemma hw6: "LF S \<Longrightarrow> S = S" by (rule refl)

axiomatization t2 :: "nat ring" where t2: "cring t2"

lemma "True"
proof -
  interpret J: LF t2 by (simp add: LF_def UP_cring_def t2)
  ML_prf \<open>
  local
    val ctxt = \<^context>;
    val X = Var (("X", 0), \<^typ>\<open>nat ring\<close>);
    val lf_X = HOLogic.mk_Trueprop (Const (\<^const_name>\<open>LF\<close>, \<^typ>\<open>nat ring \<Rightarrow> bool\<close>) $ X);
    fun results tac t = map (Thm.prop_of o Goal.conclude) (Seq.list_of (tac (Goal.init (Thm.cterm_of ctxt t))));
  in
  val _ = check_rows
   [("instance_tac newest first", fn () =>
      results (Light_Locale_Axiom_Facts.instance_tac ctxt 1) lf_X = [\<^prop>\<open>LF t2\<close>, \<^prop>\<open>LF t\<close>]),
    ("resolve_closing_setclass_prems two results", fn () =>
      results (Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt @{thms hw6} 1) (HOLogic.mk_Trueprop (HOLogic.mk_eq (X, X))) =
        [\<^prop>\<open>t2 = t2\<close>, \<^prop>\<open>t = t\<close>])]
  end
  \<close>
  show ?thesis by (rule TrueI)
qed

end
