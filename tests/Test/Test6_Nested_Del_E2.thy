(* Plan section 7 test 6, leaf E2 (plan lines 4416-4417): in the declaration block, declare fooE9c
   [rule del] with the local name deletes both copies -- the positive control first (the theory's
   claset has a rule with LF.fooE9c's proposition), then neither the block's nor the theory's
   claset has one. *)
theory Test6_Nested_Del_E2
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"
ML \<open>val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;\<close>

context LF begin
lemma fooE9c [elim]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
ML_val \<open>
val _ = \<^assert> (not (null (claset_entries \<^context> @{thm fooE9c})));
val _ = \<^assert> (not (null (claset_entries (thy_ctxt \<^context>) @{thm LF.fooE9c})));
\<close>
declare fooE9c [rule del]
ML_val \<open>
val _ = \<^assert> (null (claset_entries \<^context> @{thm fooE9c}));
val _ = \<^assert> (null (claset_entries (thy_ctxt \<^context>) @{thm LF.fooE9c}));
\<close>
end

ML \<open>val _ = \<^assert> (null (claset_entries \<^context> @{thm LF.fooE9c}));\<close>

end
