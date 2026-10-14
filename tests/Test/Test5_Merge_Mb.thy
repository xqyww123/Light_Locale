(* The merge of two syntax-only registrations of the same key: the effect set is the union. *)
theory Test5_Merge_Mb
  imports Test5_Merge_S1 Test5_Merge_S2b
begin

ML \<open>
val _ = \<^assert> (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] =
  [([\<^term>\<open>t\<close>], Locale.Syntax_only, ["Q.x", "I.x"])]);
\<close>

end
