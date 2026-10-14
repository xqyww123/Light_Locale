(* Plan section 7 test 6, row (iii) of the Rule_Cases group: on plain HOL facts without tags the
   patched induct behaves as stock -- a chained fact with an induct rule selects it, a rule-less
   first fact makes the method fall back to the type rules (found by a type-variable query,
   induct.ML:773-778; the plan's "Unable to figure out induct rule" does not occur on stock either,
   section 11 item (21)).  No light locale in this leaf. *)
theory Test6_Cases_HOL
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Qx :: "nat \<Rightarrow> bool"
inductive ev' :: "nat \<Rightarrow> bool" where "ev' 0" | "ev' n \<Longrightarrow> ev' (Suc (Suc n))"

ML \<open>
val (h1, ctxt1) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "h1" "Qx n";
val (h2, ctxt2) = assume_in ctxt1 [] "h2" "ev' n";
val _ = \<^assert> (case_names (run ctxt2 [h2] "induct" "W n") = ["1", "2"]);
val _ = \<^assert> (case_names (run ctxt2 [h2, h1] "induct" "W n") = ["1", "2"]);
val _ = \<^assert> (case_names (run ctxt2 [h1, h2] "induct" "W n") <> ["1", "2"]);
val _ = \<^assert> (case_names (run ctxt2 [h1, h2] "induct" "W n") = case_names (run ctxt1 [h1] "induct" "W n"));
\<close>

end
