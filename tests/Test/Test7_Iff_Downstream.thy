(* Plan section 7 test 7, plan lines 4915-4916, downstream of Test7_Iff (no interpretation of LI):
   a goal that does not need the rule, with Rc a b among its hypotheses and a conclusion safe
   cannot close by assumption, (EX x. ALL y. R x y) ==> ALL y. EX x. R x y: apply safe runs out of
   safe rules with Rc a b still a hypothesis, leaves one subgoal (as the heavy twin's theory-level
   row in Test7_Iff_Heavy) and no subgoal mentioning LI (the theory copy's halves are unsafe; the
   safe iff rule was the block's local copy), and by auto succeeds. *)
theory Test7_Iff_Downstream
  imports Test7_Iff
begin

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val goal = "Rc (a :: 'q) (b :: nat) \<Longrightarrow> (\<exists>x. \<forall>y. R x y) \<Longrightarrow> \<forall>y. \<exists>x. R x y";
(*measured: the one subgoal is !!x y. [| Rc a b; ALL y. R x y |] ==> EX x. R x y*)
val sgs = goal_prems (run_apply ctxt [] "safe" goal);
val _ = \<^assert> (length sgs = 1);
val _ = \<^assert> (not (exists (Term.exists_Const (fn (c, _) => c = \<^const_name>\<open>LI\<close>)) sgs));
val _ = \<^assert> (by_method ctxt [] "auto" goal);
\<close>

end
