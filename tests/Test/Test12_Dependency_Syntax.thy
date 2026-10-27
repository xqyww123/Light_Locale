(* Plan section 7 test 12 (repair phase, step 1), the Syntax_only variant of A7 (batch-1 plan
   section 4.1, A7'): heavy Y, light X = Y, interpretation I: X t (Y gets a Syntax_only
   registration), then sublocale Y < LF r; the graded add_dependency reaches the light LF and its
   Axiom note puts LF t into the theory's table. *)
theory Test12_Dependency_Syntax
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

axiomatization t :: "nat ring" where t: "cring t"

locale Y = fixes r :: "nat ring" assumes yr: "cring r"
light_locale X = Y

interpretation I: X t by (simp add: X_def Y_def t)

ML \<open>check_rows [("A7' before", fn () => null (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LF t\<close>))]\<close>

sublocale Y \<subseteq> LF r by (simp add: LF_def UP_cring_def yr)

ML \<open>check_rows [("A7'", fn () => retrieves \<^context> \<^prop>\<open>LF t\<close>)]\<close>

end
