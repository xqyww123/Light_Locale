(* Plan section 7 test 12 (repair phase, step 1), the table after interpret in a proof (batch-1
   plan section 4.1, A4): the fact is retrieved in that proof and not at theory level, before or
   after. *)
theory Test12_Table_Interpret
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

ML \<open>check_rows [("A4 before", fn () => null (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LF t\<close>))]\<close>

lemma "True"
proof -
  interpret I: LF t by (simp add: LF_def UP_cring_def t)
  ML_prf \<open>check_rows [("A4 proof", fn () => retrieves_only \<^context> \<^prop>\<open>LF t\<close> @{thm I.LF_axioms})]\<close>
  show ?thesis by (rule TrueI)
qed

ML \<open>check_rows [("A4 after", fn () => null (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LF t\<close>))]\<close>

end
