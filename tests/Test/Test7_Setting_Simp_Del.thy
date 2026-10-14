(* Plan section 7 test 7: when the block exports no premise, [simp del] of a theory fact inside the block is global (section 5.7): the theory copy is tsimp2 itself.  Positive controls before; after context Setting begin declare tsimp2 [simp del] end, k1 = 0 is no longer proved by simp at theory level; after the heavy twin's context Setting0 begin declare tsimp3 [simp del] end, k2 = 0 still is. *)
theory Test7_Setting_Simp_Del
  imports Test_Support
begin

ML \<open>open Test_Support\<close>


light_locale Setting = fixes n :: nat
locale Setting0 = fixes n :: nat
definition k1 :: nat where "k1 = 0"
lemma tsimp2 [simp]: "k1 = 0" by (simp add: k1_def)
definition k2 :: nat where "k2 = 0"
lemma tsimp3 [simp]: "k2 = 0" by (simp add: k2_def)

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (by_simp ctxt \<^prop>\<open>k1 = 0\<close>);
val _ = \<^assert> (by_simp ctxt \<^prop>\<open>k2 = 0\<close>);
\<close>

context Setting begin declare tsimp2 [simp del] end
context Setting0 begin declare tsimp3 [simp del] end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>k1 = 0\<close>));
val _ = \<^assert> (by_simp ctxt \<^prop>\<open>k2 = 0\<close>);
\<close>

end
