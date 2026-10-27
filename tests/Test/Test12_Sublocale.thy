(* Plan section 7 test 12 (repair phase, step 1), the table through sublocale (batch-1 plan
   section 4.1, A6): after sublocale X < LF r (X heavy) the block of X holds LF r; after
   interpretation I: X t the theory's table holds LF t.  The dependency edge is persistent theory
   state, so this leaf owns it. *)
theory Test12_Sublocale
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

locale X = fixes r :: "nat ring" assumes xr: "cring r"

sublocale X \<subseteq> LF r by (simp add: LF_def UP_cring_def xr)

context X begin
ML \<open>check_rows [("A6 block", fn () => retrieves \<^context> \<^prop>\<open>LF r\<close>)]\<close>
end

ML \<open>check_rows [("A6 before", fn () => null (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LF t\<close>))]\<close>

interpretation I: X t by (rule X.intro) (rule t)

ML \<open>check_rows [("A6 theory", fn () => retrieves \<^context> \<^prop>\<open>LF t\<close>)]\<close>

end
