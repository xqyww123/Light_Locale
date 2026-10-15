(* Plan section 7 test 7, plan lines 4918-4919, downstream of Test7_Niff (no interpretation of LN):
   a goal that needs the rule, Rc a b ==> False, is not closed by blast -- blast drops the theory
   copy's notE half as a weak elimination rule because none of its premises concludes ?R
   (classical_rule leaves it unchanged, classical.ML:150-151; blast.ML:441-447, :513-517): the same
   reason as in the reopened block (Test7_Niff) and plan section 5.7 (lines 3382-3384), unlike an
   unsafe [dest]. *)
theory Test7_Niff_Downstream
  imports Test7_Niff
begin

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (blast_warns ctxt "Rc (a :: 'q) (b :: nat) \<Longrightarrow> False" = (false, true));
\<close>

end
