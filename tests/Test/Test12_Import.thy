(* Plan section 7 test 12 (repair phase, step 1), the table through an import (batch-1 plan
   section 4.1, A8): after interpretation I: L2 t of light L2 = LF + ..., the theory's table holds
   LF t. *)
theory Test12_Import
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

light_locale L2 = LF + assumes l2: "S = S"

interpretation I: L2 t by (simp add: L2_def L2_axioms_def LF_def UP_cring_def t)

ML \<open>check_rows [("A8", fn () => retrieves \<^context> \<^prop>\<open>LF t\<close>)]\<close>

end
