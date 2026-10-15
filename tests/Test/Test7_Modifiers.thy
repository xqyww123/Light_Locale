(* Plan section 7 test 7, plan lines 4890-4905: method modifiers and explicit rules on the theory
   copies of a light block's attribute-free rules fooD, fooE0, fooI0 over consts Rd/Sd (no other
   row registers a rule on them: the bare-auto controls must fail for the rows to discriminate).
   In a reopened block: auto dest: LM.fooD, auto elim: LM.fooE0 and auto intro: LM.fooI0 close
   the goal that bare auto does not (the modifier takes the same registration path as the
   attribute; LM ?S is closed by LM_axioms [intro!]); the elim: modifier's derived rule, read
   back from the context that Token.syntax (Method.sections Classical.cla_modifiers) returns for
   the modifier text (Test_Support.cla_modified: the context a method receives, method.ML:437-438),
   has the major premise first and LM ?S second; erule LM.fooE0 fails (LM ?S is its first premise),
   erule LM.fooE0[OF LM_axioms] succeeds; erule LM.ip.cases fails, erule LM.ip.cases[OF LM_axioms]
   leaves the one subgoal x = 0 ==> x = 0 that the heavy twin's erule ip.cases leaves (the same
   literal in Test7_Modifiers_Heavy), erule LM.ip.cases[OF _ LM_axioms] reports OF: no unifiers;
   subst LM.fooS leaves one subgoal more than the twin's subst fooS, the first led by LM, subst
   LM.fooS[OF LM_axioms] as many as the twin. *)
theory Test7_Modifiers
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Rd :: 'a  Sd :: 'a
axiomatization where Sd_ax: "Sd x" and RdSd_ax: "Rd x (n :: nat) = Sd x"

light_locale LM = fixes S :: nat assumes "S = S"

context LM begin
lemma fooD: "Rd x S \<Longrightarrow> Sd x" by (rule Sd_ax)
lemma fooE0: "Rd x S \<Longrightarrow> (Sd x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sd_ax)
lemma fooI0: "Rd x S \<Longrightarrow> Sd x" by (rule Sd_ax)
lemma fooS: "Rd x S = Sd x" by (rule RdSd_ax)
inductive ip :: "nat \<Rightarrow> bool" where ip0: "ip 0"
end

context LM begin
ML_val \<open>
val ctxt = \<^context>;
val goal = "Rd (a :: 'q) S \<Longrightarrow> Sd a";
val light = Light_Locale_Axiom_Facts.is_light_prop ctxt;
(*the controls*)
val _ = \<^assert> (not (by_method ctxt [] "auto" goal));
(*the modifiers*)
val _ = \<^assert> (by_method ctxt [] "auto dest: LM.fooD" goal);
val _ = \<^assert> (by_method ctxt [] "auto elim: LM.fooE0" goal);
val _ = \<^assert> (by_method ctxt [] "auto intro: LM.fooI0" goal);
(*the derived rule the elim: modifier registers: major premise first, LM ?S second*)
val _ = \<^assert>
  (case claset_entries (cla_modified ctxt "elim: LM.fooE0") @{thm LM.fooE0} of
    [(_, plain, _)] =>
      (case Thm.prems_of plain of
        p1 :: p2 :: _ =>
          (case Term.head_of (HOLogic.dest_Trueprop p1) of Const (c, _) => c = \<^const_name>\<open>Rd\<close> | _ => false)
          andalso light p2
      | _ => false)
  | _ => false);
(*explicit rules*)
val _ = \<^assert> (not (can (run_apply ctxt [] "erule LM.fooE0") goal));
val _ = \<^assert> (by_method ctxt [] "erule LM.fooE0[OF LM_axioms]" goal);
val ip_goal = "LM.ip x \<Longrightarrow> x = 0";
val _ = \<^assert> (not (can (run_apply ctxt [] "erule LM.ip.cases") ip_goal));
(*the one subgoal x = 0 ==> x = 0, the literal the heavy twin compares with too*)
val _ = \<^assert> (eq_list (op aconv) (goal_prems (run_apply ctxt [] "erule LM.ip.cases[OF LM_axioms]" ip_goal),
  [\<^prop>\<open>(x :: nat) = 0 \<Longrightarrow> x = 0\<close>]));
(*a THM exception whose message is "OF: no unifiers" (measured: the attribute evaluation raises it)*)
val _ = \<^assert>
  (case Exn.capture (run_apply ctxt [] "erule LM.ip.cases[OF _ LM_axioms]") ip_goal of
    Exn.Exn e => String.isSuffix "OF: no unifiers" (Protocol_Message.clean_output (Runtime.exn_message e))
  | Exn.Res _ => false);
(*the rewrite equation as an argument*)
val s_goal = "Rd (a :: 'q) S";
val st = run_apply ctxt [] "subst LM.fooS" s_goal;
val _ = \<^assert> (subgoals st = 2 andalso light (Logic.strip_assums_concl (hd (goal_prems st))));
val _ = \<^assert> (subgoals (run_apply ctxt [] "subst LM.fooS[OF LM_axioms]" s_goal) = 1);
\<close>
end

end
