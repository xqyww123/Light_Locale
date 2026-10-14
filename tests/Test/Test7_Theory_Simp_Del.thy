(* Plan section 7 test 7: declare tsimp [simp del] written at theory level deletes it (own leaf: a global deletion). *)
theory Test7_Theory_Simp_Del
  imports Test_Support
begin

ML \<open>open Test_Support\<close>


definition k0 :: nat where "k0 = 0"
lemma tsimp [simp]: "k0 = 0" by (simp add: k0_def)
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k0 = 0\<close>)\<close>
declare tsimp [simp del]
ML \<open>val _ = \<^assert> (not (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k0 = 0\<close>))\<close>

end
