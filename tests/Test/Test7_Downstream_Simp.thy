(* Plan section 7 test 7: a light lemma foo [simp] of the base session is a global simp rule
   downstream -- a goal carrying LF t (its condition is discharged through LF_axioms) and the
   predicate-free Setting's bar close by simp; the standard locale's twin does not. *)
theory Test7_Downstream_Simp
  imports Test_Support "Light_Locale_Base.Base_Downstream_Simp"
begin

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*Test_Support.by_simp is asm_full_simp_tac: foo's condition LFds t is discharged from the goal's premise*)
val by_simp = Test_Support.by_simp ctxt;
val _ = \<^assert> (by_simp \<^prop>\<open>LFds t \<Longrightarrow> kd t = 0\<close>);
val _ = \<^assert> (by_simp \<^prop>\<open>kd {n} = 0\<close>);
val _ = \<^assert> (not (by_simp \<^prop>\<open>Dds t \<Longrightarrow> kd0 t = 0\<close>));
\<close>

end
