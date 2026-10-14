(* Plan section 7 test 6 (plan lines 4715-4716): attribute order does not matter -- lemma fooE
   [elim, consumes 1, case_names Hyp] in the declaration block, end, reopen, declare LF.fooE [rule
   del] succeeds without "Undeclared classical rule" and the claset has no entry with its
   proposition. *)
theory Test6_Del_FooE
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooE [elim, consumes 1, case_names Hyp]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
ML_val \<open>\<^assert> (not (null (claset_entries \<^context> @{thm LF.fooE})))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.fooE" "[rule del]")
  in \<^assert> (not (exists (String.isPrefix "Undeclared classical rule") w)); lthy' end\<close>
ML_val \<open>\<^assert> (null (claset_entries \<^context> @{thm LF.fooE}))\<close>
end

end
