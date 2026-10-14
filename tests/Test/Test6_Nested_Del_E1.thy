(* Plan section 7 test 6, deletion in a nested block, leaf E1 (plan lines 4410-4415): fooE9 [elim?]
   in the outer block (Context_Rules), end, reopen, and in a nested assumes block declare LF.fooE9
   [Pure.rule del]: declared_rule is true before and false after, and after both blocks close the
   theory's Context_Rules has lost it too.  The heavy twin's nested-block short-name declare fooE9
   [Pure.rule del] deletes its replayed copy, the literal declare D.fooE9 [Pure.rule del] deletes
   nothing.  The Classical companion: fooE9c [elim], reopen, nested declare LF.fooE9c [rule del]
   without warning, gone from Classical.dest_decls. *)
theory Test6_Nested_Del_E1
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a  Qc :: 'a
axiomatization where Sc_ax: "Sc x"

ML \<open>
fun declared ctxt th = Context_Rules.declared_rule (Context.Proof ctxt) th;
val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;
\<close>

context D begin
lemma fooE9 [elim?]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end
context D begin
context fixes y assumes hy: "Qc y" begin
ML_val \<open>\<^assert> (declared \<^context> @{thm fooE9})\<close>
declare D.fooE9 [Pure.rule del]
ML_val \<open>\<^assert> (declared \<^context> @{thm fooE9})\<close>
declare fooE9 [Pure.rule del]
ML_val \<open>\<^assert> (not (declared \<^context> @{thm fooE9}))\<close>
end
end

context LF begin
lemma fooE9 [elim?]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma fooE9c [elim]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
context fixes y assumes hy: "Qc y" begin
ML_val \<open>\<^assert> (declared \<^context> @{thm LF.fooE9})\<close>
declare LF.fooE9 [Pure.rule del]
ML_val \<open>\<^assert> (not (declared \<^context> @{thm LF.fooE9}))\<close>
ML_val \<open>\<^assert> (not (null (claset_entries \<^context> @{thm LF.fooE9c})))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.fooE9c" "[rule del]")
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>\<^assert> (null (claset_entries \<^context> @{thm LF.fooE9c}))\<close>
end
end

ML \<open>
val _ = \<^assert> (not (declared \<^context> @{thm LF.fooE9}));
val _ = \<^assert> (null (claset_entries \<^context> @{thm LF.fooE9c}));
\<close>

end
