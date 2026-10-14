(* Plan section 7 test 6 (plan lines 4718-4719): lemma fooE' [elim?, consumes 1] in the declaration
   block, end, reopen, Context_Rules.declared_rule is true for LF.fooE', declare LF.fooE' [Pure.rule
   del] removes it (declared_rule false; Context_Rules never warns). *)
theory Test6_Del_PureRule
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooE' [elim?, consumes 1]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
ML_val \<open>\<^assert> (Context_Rules.declared_rule (Context.Proof \<^context>) @{thm LF.fooE'})\<close>
declare LF.fooE' [Pure.rule del]
ML_val \<open>\<^assert> (not (Context_Rules.declared_rule (Context.Proof \<^context>) @{thm LF.fooE'}))\<close>
end

ML \<open>val _ = \<^assert> (not (Context_Rules.declared_rule (Context.Proof \<^context>) @{thm LF.fooE'}));\<close>

end
