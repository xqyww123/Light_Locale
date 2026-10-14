(* Plan section 7 test 6 (plan line 4747), the [intro!] polarity twin: downstream of a light
   block's fooI [intro!] (the theory copy LF ?S ==> Pc ?x ==> Sc ?x is a global safe introduction
   rule), a goal with the conclusion Sc a that the simplifier cannot close (its universal
   assumptions are conditional on a disjunction) and whose safe steps are disjE and, on each
   branch, the rule: safe leaves LF ?S twice (schematic, nothing closes it -- an intro! rule has no
   classical_rule form, so there is no negated conclusion to refute it from); the standard
   control's auto closes the goal, the light auto leaves the two light subgoals.  Section 11 item
   (27). *)
theory Test6_Intro_Bang
  imports Test_Support "Light_Locale_Base.Base_Intro_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
val goal = \<^prop>\<open>Pc (a :: 'q) \<Longrightarrow> Q a \<or> R a \<Longrightarrow> \<forall>x :: 'q. Q x \<longrightarrow> Sc x \<Longrightarrow> \<forall>x :: 'q. R x \<longrightarrow> Sc x \<Longrightarrow> Sc a\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
val light_concls = forall (light o Logic.strip_assums_concl) o goal_prems;
val _ = \<^assert> (not (by_simp \<^context> goal));
(* safe: disjE, then the rule on each branch, leaving LF ?S *)
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 2 andalso light_concls st);
(* without the rule, safe stops at Sc a on each branch *)
val st = proof_after {apply = true} \<^context> [] "safe del: LF.fooI" goal;
val _ = \<^assert> (subgoals st = 2 andalso not (exists (light o Logic.strip_assums_concl) (goal_prems st)));
(* the row: the standard control's auto closes the goal, the light auto does not *)
val _ = \<^assert> (subgoals (proof_after {apply = true} \<^context> [] "auto del: LF.fooI" goal) = 0);
val st = proof_after {apply = true} \<^context> [] "auto" goal;
val _ = \<^assert> (subgoals st > 0 andalso light_concls st);
\<close>

end
