(* Plan section 7 test 7: declare tsimp [simp del] written at theory level deletes it (own leaf: a global deletion). *)
theory Test7_Theory_Simp_Del
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_simp = proves (fn c => simp_tac c 1);
val by_safe = proves safe_tac;
val by_clarify = proves (fn c => clarify_tac c 1);
val by_clarsimp = proves (fn c => clarsimp_tac c 1);
val by_blast = proves (fn c => blast_tac c 1);
fun ws f = #2 (with_warnings f);
\<close>

definition k0 :: nat where "k0 = 0"
lemma tsimp [simp]: "k0 = 0" by (simp add: k0_def)
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k0 = 0\<close>)\<close>
declare tsimp [simp del]
ML \<open>val _ = \<^assert> (not (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k0 = 0\<close>))\<close>

end
