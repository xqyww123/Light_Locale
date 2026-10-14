(* Plan section 7 test 6 (plan line 4601): a cases rule without own premises, declare LF.z0 [cases
   pred: Sc] in the reopened block is accepted and keyed on LF ?S (own_major_prem falls back to the
   major premise); only acceptance and the key are asserted. *)
theory Test6_Exported_CasesPred
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma z0: "Sc x" by (rule Sc_ax)
end

context LF begin
declare LF.z0 [cases pred: Sc]
ML_val \<open>\<^assert> (is_some (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>LF S\<close> @{thm LF.z0}))\<close>
end

end
