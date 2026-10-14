(* Plan section 7 test 6 (plan lines 4602-4604): declare LF.z0 [cases type: nat] in the reopened
   block is accepted (left_var_prem reads the original theorem's first premise LF ?S when there is
   no own premise), as the heavy twin's theory-level declare D.z0 [cases type: nat]; only the
   acceptance is asserted. *)
theory Test6_Exported_CasesType
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma z0: "Sc x" by (rule Sc_ax)
end
context D begin
lemma z0: "Sc x" by (rule Sc_ax)
end

ML \<open>val _ = \<^assert> (can (fn () => declare_in (Named_Target.theory_init \<^theory>) "D.z0" "[cases type: nat]") ());\<close>

context LF begin
local_setup \<open>fn lthy => declare_in lthy "LF.z0" "[cases type: nat]"\<close>
end

end
