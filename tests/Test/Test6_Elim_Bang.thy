(* Plan section 7 test 6 (plan lines 4424-4427): downstream of a light block's bad4 [elim!] -- the
   theory copy is a global safe elimination rule whose derived form puts the exported premise
   LF ?S second -- a goal that does not need the rule, has Rc a b among its assumptions and whose
   conclusion needs that assumption: apply safe eliminates Rc a b and leaves LF b as the first
   subgoal, by auto leaves a light subgoal (the safe phase consumed the assumption the conclusion
   needs), while downstream of the heavy twin -- the theory without the rule -- auto closes the
   goal.  Section 11 item (26). *)
theory Test6_Elim_Bang
  imports Test_Support "Light_Locale_Base.Base_Elim_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
(* b has the type of the locale parameter, so that the rule applies to Rc a b; the conclusion needs
   Rc a b itself (and the unsafe exI), so that safe's only step is the elimination of Rc a b *)
val goal = \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
(* plan line 4426: simp alone does not close the goal *)
val _ = \<^assert> (not (by_simp \<^context> goal));
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 2 andalso
  Logic.strip_assums_concl (hd (goal_prems st)) aconv \<^prop>\<open>LF (b :: ('z, 'w) ring_scheme)\<close>);
val st = proof_after {apply = true} \<^context> [] "auto" goal;
val _ = \<^assert> (subgoals st > 0 andalso light (Logic.strip_assums_concl (hd (goal_prems st))));
val _ = \<^assert> (subgoals (proof_after {apply = true} \<^context> [] "auto del: LF.bad4" goal) = 0);
(* without the rule, safe has no step at all (the method fails): the elimination was its only step;
   the same method text closes a goal that needs no rule, so a misread of the text cannot pass
   the negative row (plan line 3792) *)
val safe_del = "safe del: LF.bad4";
val _ = \<^assert> (subgoals (proof_after {apply = true} \<^context> [] safe_del
  \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Rc a b\<close>) = 0);
val _ = \<^assert> (not (can (fn () => proof_after {apply = true} \<^context> [] safe_del goal) ()));
\<close>

end
