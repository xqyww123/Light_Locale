(* Plan section 7 test 12 (repair phase, step 1), the table when the dependency comes after the
   registration (batch-1 plan section 4.1, A7): interpretation I: X t, then sublocale X < LF r
   (X heavy); add_dependency's re-registration puts LF t into the theory's table. *)
theory Test12_Dependency
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

locale X = fixes r :: "nat ring" assumes xr: "cring r"

interpretation I: X t by (rule X.intro) (rule t)

ML \<open>check_rows [("A7 before", fn () => null (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LF t\<close>))]\<close>

sublocale X \<subseteq> LF r by (simp add: LF_def UP_cring_def xr)

ML \<open>check_rows [("A7", fn () => retrieves \<^context> \<^prop>\<open>LF t\<close>)]\<close>

end
