(* The merge (Heavy side): imports A and B, runs step 5 -- definition (in HB) dd: exactly one I.dd,
   J.dd present. *)
theory Test5_SibH_M
  imports Test5_SibH_A Test5_SibH_B
begin

definition (in HB) dd where "dd = x"

ML \<open>
val _ = \<^assert> (length (filter (String.isSuffix "I.dd") (Test_Support.consts_named (Proof_Context.init_global \<^theory>) "dd")) = 1);
val _ = \<^assert> (exists (String.isSuffix "J.dd") (Test_Support.consts_named (Proof_Context.init_global \<^theory>) "dd"));
\<close>

end
