(* Plan section 7 test 4 (upgrade): the control group of groups (a) and (b) -- a theory that has
   never seen LF; interpretation Ctl: HB t installs exactly the names hb_installed, which (a) and
   (b) compare their two commands' union against. *)
theory Test4_Control
  imports Test4_Fixture
begin

interpretation Ctl: HB t by unfold_locales simp

ML \<open>
val _ = \<^assert> (map (unprefix "Test4_Control.Ctl.") (Test_Support.facts_under \<^theory> "Test4_Control.Ctl.") = hb_installed);
\<close>

end
