(* Plan section 7 test 6 (plan lines 4421-4424): the [dest!] twin of Test6_Elim_Bang. *)
theory Test6_Dest_Bang
  imports Test_Support "Light_Locale_Base.Base_Dest_Bang"
begin

ML \<open>open Test_Support\<close>
ML \<open>
val goal = \<^prop>\<open>Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x\<close>;
val light = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
val st = proof_after {apply = true} \<^context> [] "safe" goal;
val _ = \<^assert> (subgoals st = 2 andalso light (Logic.strip_assums_concl (hd (Thm.prems_of (#goal (Proof.goal st))))));
val _ = \<^assert> (can (fn () => proof_after {apply = false} \<^context> [] "auto" goal) ());
(* without the rule, safe has no step at all (the method fails): the elimination was its only step *)
val _ = \<^assert> (not (can (fn () => proof_after {apply = true} \<^context> [] "safe del: LF.bad4d" goal) ()));
\<close>

end
