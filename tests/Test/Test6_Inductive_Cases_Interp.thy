(* Plan section 7 test 6 (plan line 4692): after interpretation I: LF t0, inductive_cases on the
   instance t0 has no extra premise (I.LF_axioms is a simp rule).  Its own leaf: a theory-level
   registration. *)
theory Test6_Inductive_Cases_Interp
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"
axiomatization t0 :: "nat ring" where t0: "cring t0"

context LF begin
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
inductive_cases ipE: "ip (Suc n)"
end

interpretation I: LF t0 by (simp add: LF_def UP_cring_def t0)

inductive_cases ipE4: "LF.ip t0 (Suc n)"
ML \<open>
val _ = \<^assert> (not (exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of @{thm ipE4})));
val _ = \<^assert> (Thm.nprems_of @{thm ipE4} = Thm.nprems_of @{thm LF.ipE} - 1);
(* the ind_cases method on the instance: no light subgoal, one subgoal per case of ipE4 *)
val ctxt = fix_in \<^context> [("n", \<^typ>\<open>nat\<close>)];
val st = run_apply ctxt [] "ind_cases \"LF.ip t0 (Suc n)\"" "LF.ip t0 (Suc n) \<Longrightarrow> W";
val _ = \<^assert> (not (exists (Light_Locale_Axiom_Facts.is_light_prop ctxt) (goal_prems st)) andalso
  subgoals st = Thm.nprems_of @{thm ipE4} - 1);
\<close>

end
