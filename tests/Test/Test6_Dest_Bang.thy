(* Plan section 7 test 6 (plan lines 4421-4427): the [dest!] twin of Test6_Elim_Bang. *)
theory Test6_Dest_Bang
  imports Test_Support "Light_Locale_Base.Base_Dest_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
val goal = \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
val _ = \<^assert> (not (by_simp \<^context> goal));
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 2 andalso
  Logic.strip_assums_concl (hd (goal_prems st)) aconv \<^prop>\<open>LF (b :: ('z, 'w) ring_scheme)\<close>);
val st = proof_after {apply = true} \<^context> [] "auto" goal;
val _ = \<^assert> (subgoals st > 0 andalso light (Logic.strip_assums_concl (hd (goal_prems st))));
val _ = \<^assert> (subgoals (proof_after {apply = true} \<^context> [] "auto del: LF.bad4d" goal) = 0);
(* without the rule, safe has no step at all (the method fails); the same method text closes a
   goal that needs no rule (plan line 3792) *)
val safe_del = "safe del: LF.bad4d";
val _ = \<^assert> (subgoals (proof_after {apply = true} \<^context> [] safe_del
  \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Rc a b\<close>) = 0);
val _ = \<^assert> (not (can (fn () => proof_after {apply = true} \<^context> [] safe_del goal) ()));
\<close>

end
