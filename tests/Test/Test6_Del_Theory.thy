(* Plan section 7 test 6 (plan line 4714): at theory level, declare LF.bad[dest], the control
   lemma "LF S ==> Rc x S ==> Sc x" by blast, declare LF.bad[rule del] without "Undeclared
   classical rule", and blast no longer closes it. *)
theory Test6_Del_Theory
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma bad: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

declare LF.bad[dest]
ML \<open>val _ = \<^assert> (by_blast \<^context> \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Sc x\<close>);\<close>
setup \<open>fn thy =>
  let
    val (lthy', w) = with_warnings (fn () => declare_in (Named_Target.theory_init thy) "LF.bad" "[rule del]");
    val _ = \<^assert> (not (exists (String.isPrefix "Undeclared classical rule") w));
  in Local_Theory.exit_global lthy' end\<close>
ML \<open>val _ = \<^assert> (not (by_blast \<^context> \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Sc x\<close>));\<close>

end
