(* Leaf 1 over the merge of two syntax-only registrations: interpretation Q: HB t installs only the
   Plain notes (Q is a recorded effect), without Duplicate fact declaration. *)
theory Test5_Merge_L1
  imports Test5_Merge_Mb
begin

interpretation Q: HB t by unfold_locales simp

ML \<open>
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test5_Merge_L1." = ["Test5_Merge_L1.Q.hb"]);
val _ = \<^assert> (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
\<close>

end
