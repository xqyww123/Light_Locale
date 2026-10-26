(* Plan section 7 test 6 (plan lines 4663-4667): the stock rule of a nested assumption's predicate
   comes first.  In the predicate-free SetF, inductive ipn in a nested context fixes A assumes hfin:
   "finite A" is stored as SetF.ipn.cases with K 1 (the nested assumption is its exported premise);
   in a reopened nested block of the same shape, with h: SetF.ipn n A a, "using hfin h proof (cases
   rule: SetF.ipn.cases)" gives the cases ipn_in / ipn_n -- the gate row.  The plan says to record,
   not gate, the stored proposition and what the unnamed "using hfin h proof cases" selects
   (finite.cases through the 0th chained fact: its cases emptyI / insertI, ipn_in undefined); those
   are evidence assertions pinning the values measured on the first build (section 11, item (23)):
   a mismatch is re-measured, not bug-hunted. *)
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
(* evidence: the stored proposition *)
val _ = \<^assert> (Thm.prop_of @{thm SetF.ipn.cases} aconv Logic.varify_global
  \<^prop>\<open>finite A \<Longrightarrow> SetF.ipn n A a \<Longrightarrow> (\<And>x. a = x \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> (a = n \<Longrightarrow> P) \<Longrightarrow> P\<close>);
\<close>

context SetF begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
ML \<open>local
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>nat\<close>)] "h" "SetF.ipn n A a";
(* gate *)
val _ = \<^assert> (case_names (run ctxt [@{thm hfin}, h] "cases rule: SetF.ipn.cases" "W a") = ["ipn_in", "ipn_n"]);
(* evidence: the unnamed form *)
val st = run ctxt [@{thm hfin}, h] "cases" "W a";
val _ = \<^assert> (case_names st = ["emptyI", "insertI"]);
val _ = \<^assert> ((Proof_Context.check_case (Proof.context_of st) true ("ipn_in", Position.none) []; false)
  handle ERROR msg => String.isPrefix "Undefined case" (Protocol_Message.clean_output msg));
in end\<close>
end
end

end
