(* Plan section 7 test 6 (plan lines 4421-4424): downstream of a light block's bad4 [elim!] -- the
   theory copy is a global safe elimination rule whose derived form puts the exported premise
   LF ?S second -- a goal that does not need the rule, has Rc a b among its assumptions and whose
   conclusion needs an unsafe step: apply safe eliminates Rc a b and leaves LF b as the first
   subgoal (with the negated conclusion among its assumptions, classical_rule's form), while the
   heavy twin's safe leaves the goal alone (its rule stays in the block).  by auto closes the goal
   on both sides: the LF b subgoal is refuted from its contradictory assumptions (section 11 item
   (26); the plan's "by auto fails" does not hold for any registration of the theory copy). *)
theory Test6_Elim_Bang
  imports Test_Support "Light_Locale_Base.Base_Elim_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
(* b has the type of the locale parameter, so that the rule applies to Rc a b; the conclusion
   needs an unsafe step (exI), so that safe's only step is the elimination of Rc a b *)
val goal = \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 2 andalso light (Logic.strip_assums_concl (hd (Thm.prems_of (#goal (Proof.goal st))))));
val _ = \<^assert> (can (fn () => proof_after {apply = false} \<^context> [] "auto" goal) ());
(* without the rule, safe has no step at all (the method fails): the elimination was its only step *)
val _ = \<^assert> (not (can (fn () => proof_after {apply = true} \<^context> [] "safe del: LF.bad4" goal) ()));
\<close>

end
