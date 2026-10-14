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
val plains = map #2 (claset_entries \<^context> @{thm LF.fooD0});
val _ = \<^assert> (exists (fn plain => Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of plain))) plains);
val hplains = map #2 (claset_entries \<^context> @{thm D.fooD0});
val _ = \<^assert> (exists (fn plain => exists (fn hplain =>
    phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (plain, hplain)) hplains) plains);
\<close>

end
