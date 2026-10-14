(* Plan section 7 test 6 (plan lines 4626-4628): at theory level declare LF.fooD0[exported_premises
   0, dest] registers a dest rule whose derived rule has LF ?S as its first premise, as the heavy
   twin's D.fooD0 [dest]. *)
theory Test6_Exported_Dest
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end
context D begin
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

declare LF.fooD0[exported_premises 0, dest]
declare D.fooD0 [dest]

ML \<open>
(* the one derived rule, literally the plan's (line 4620), and the twin's under phi *)
val (_, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.fooD0};
val _ = \<^assert> (same_shape (Thm.prop_of plain,
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
val (_, hplain) = claset_rule \<^context> Bires.dest_kind @{thm D.fooD0};
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (plain, hplain));
\<close>

end
