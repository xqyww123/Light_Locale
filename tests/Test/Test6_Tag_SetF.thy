(* Plan section 7 test 6 (plan lines 4663-4668): the stock rule of a nested assumption's predicate
   comes first.  In the predicate-free SetF, inductive ipn in a nested context fixes A assumes hfin:
   "finite A" is stored as SetF.ipn.cases with K 1 (the nested assumption is its exported premise);
   in a reopened nested block of the same shape, with h: SetF.ipn n A a, "using hfin h proof (cases
   rule: SetF.ipn.cases)" gives the cases ipn_in / ipn_n (the gate), while the unnamed "using hfin h
   proof cases" selects finite.cases through the 0th chained fact (its cases emptyI / insertI, and
   ipn_in is undefined) -- the evidence recorded in section 11 item (23). *)
theory Test6_Tag_SetF
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

light_locale SetF = fixes n :: nat
context SetF begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
inductive ipn :: "nat \<Rightarrow> bool" where ipn_in: "x \<in> A \<Longrightarrow> ipn x" | ipn_n: "ipn n"
end
end

ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm SetF.ipn.cases} = 1);
val _ = \<^assert> (Thm.prop_of @{thm SetF.ipn.cases} aconv Logic.varify_global
  \<^prop>\<open>finite A \<Longrightarrow> SetF.ipn n A a \<Longrightarrow> (\<And>x. a = x \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> (a = n \<Longrightarrow> P) \<Longrightarrow> P\<close>);
\<close>

context SetF begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
ML_val \<open>
fun run ctxt facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>nat\<close>)] "h" "SetF.ipn n A a";
val _ = \<^assert> (case_names (run ctxt [@{thm hfin}, h] "cases rule: SetF.ipn.cases" "W a") = ["ipn_in", "ipn_n"]);
(* evidence *)
val st = run ctxt [@{thm hfin}, h] "cases" "W a";
val _ = \<^assert> (case_names st = ["emptyI", "insertI"]);
val _ = \<^assert> ((Proof_Context.check_case (Proof.context_of st) true ("ipn_in", Position.none) []; false)
  handle ERROR msg => String.isPrefix "Undefined case" (XML.content_of (YXML.parse_body msg)));
\<close>
end
end

end
