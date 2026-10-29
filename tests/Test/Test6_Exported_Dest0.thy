(* Plan section 7 test 6 (plan lines 4626-4628), the control: at theory level declare LF.fooD0 [dest]
   without [setclass 0] registers a derived rule whose major premise is Rc ?x ?S. *)
theory Test6_Exported_Dest0
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

declare LF.fooD0 [dest]

ML \<open>
(* the one derived rule, literally the plan's (line 4606) *)
val (_, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.fooD0};
val _ = \<^assert> (same_shape (Thm.prop_of plain,
  Logic.varify_global \<^prop>\<open>Rc x S \<Longrightarrow> LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
\<close>

end
