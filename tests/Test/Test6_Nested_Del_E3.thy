(* Plan section 7 test 6, leaf E3 (plan lines 4420-4421): in the declaration block, declare
   LF.fooE9c [rule del] deletes the theory copy's registration, the block's local registration
   stays, and with_warnings catches "Undeclared classical rule" (the block's pass finds no
   LF.fooE9c in the block's claset). *)
theory Test6_Nested_Del_E3
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooE9c [elim]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
ML_val \<open>\<^assert> (not (null (claset_entries (thy_ctxt \<^context>) @{thm LF.fooE9c})))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.fooE9c" "[rule del]")
  in \<^assert> (exists (String.isPrefix "Undeclared classical rule") w); lthy' end\<close>
ML_val \<open>
val _ = \<^assert> (null (claset_entries (thy_ctxt \<^context>) @{thm LF.fooE9c}));
val _ = \<^assert> (not (null (claset_entries \<^context> @{thm fooE9c})));
\<close>
end

end
