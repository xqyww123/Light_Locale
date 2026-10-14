(* Plan section 7 test 6 (plan line 4747), the [intro!] polarity twin: downstream of a light
   block's fooI [intro!] (the theory copy LF ?S ==> Pc ?x ==> Sc ?x is a global safe introduction
   rule), a goal with the conclusion Sc a whose only safe step is that rule: safe leaves LF ?S
   (schematic, nothing closes it), without the rule safe has no step, and "safe, auto" fails;
   auto itself closes the goal on both sides -- its simplifier uses the universal assumption first
   (section 11 item (27)). *)
theory Test6_Intro_Bang
  imports Test_Support "Light_Locale_Base.Base_Intro_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
val goal = \<^prop>\<open>Pc (a :: 'q) \<Longrightarrow> \<forall>x :: 'q. Sc x \<Longrightarrow> Sc a\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
(* safe's only step is the rule; it leaves LF ?S, which nothing closes *)
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 1 andalso light (Logic.strip_assums_concl (hd (Thm.prems_of (#goal (Proof.goal st))))));
val _ = \<^assert> (not (can (fn () => proof_after {apply = true} \<^context> [] "safe del: LF.fooI" goal) ()));
val _ = \<^assert> (not (can (fn () => proof_after {apply = false} \<^context> [] "safe, auto" goal) ()));
(* auto itself still closes the goal: its simplifier uses the universal assumption before the
   classical step; the heavy twin's auto closes it too *)
val _ = \<^assert> (can (fn () => proof_after {apply = false} \<^context> [] "auto" goal) ());
val _ = \<^assert> (can (fn () => proof_after {apply = false} \<^context> [] "auto del: LF.fooI" goal) ());
\<close>

end
