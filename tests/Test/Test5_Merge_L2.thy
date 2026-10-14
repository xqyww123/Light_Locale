(* Leaf 2: interpretation R: HB t (a new named effect) installs everything under R. *)
theory Test5_Merge_L2
  imports Test5_Merge_Mb
begin

interpretation R: HB t by unfold_locales simp

ML \<open>
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test5_Merge_L2." = ["Test5_Merge_L2.R.HB_axioms", "Test5_Merge_L2.R.hb"]);
\<close>

end
