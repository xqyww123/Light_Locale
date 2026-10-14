(* Leaf 3, the clean upgrade: after R: HB t the key carries one Full_mark, and a further
   interpretation Q: HB t is redundant -- nothing is installed, no Duplicate fact declaration. *)
theory Test5_Merge_L3
  imports Test5_Merge_Mb
begin

interpretation R: HB t by unfold_locales simp
interpretation Q: HB t by unfold_locales simp

ML \<open>
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test5_Merge_L3." = ["Test5_Merge_L3.R.HB_axioms", "Test5_Merge_L3.R.hb"]);
val _ = \<^assert> (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
\<close>

end
