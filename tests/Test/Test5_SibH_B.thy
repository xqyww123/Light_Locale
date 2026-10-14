(* Sibling B (Heavy side): steps 1 and 2 -- I: LF x for x, then I: K. *)
theory Test5_SibH_B
  imports Test5_SibH_T0
begin

interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test5_SibH_B.I." =
  ["Test5_SibH_B.I.HB_axioms", "Test5_SibH_B.I.K_axioms", "Test5_SibH_B.I.LF_axioms", "Test5_SibH_B.I.hb", "Test5_SibH_B.I.hbx"]);
\<close>

end
