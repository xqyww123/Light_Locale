(* The merge (Light side): imports A and B, runs step 5 -- definition (in HB) dd: exactly one I.dd,
   J.dd present, and the record of HB [?x, c] is Syntax_only with effect I. *)
theory Test5_Sib_M
  imports Test5_Sib_A Test5_Sib_B
begin

definition (in HB) dd where "dd = x"

ML \<open>
val xc = [Var (("x", 0), \<^typ>\<open>nat\<close>), \<^term>\<open>c\<close>];
val _ = \<^assert> (exists (fn (inst, level, effects) =>
    eq_list (op aconv) (inst, xc) andalso level = Locale.Syntax_only andalso member (op =) effects "I.x")
  (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" xc));
val _ = \<^assert> (length (filter (String.isSuffix "I.dd") (Test_Support.consts_named (Proof_Context.init_global \<^theory>) "dd")) = 1);
val _ = \<^assert> (exists (String.isSuffix "J.dd") (Test_Support.consts_named (Proof_Context.init_global \<^theory>) "dd"));
\<close>

end
