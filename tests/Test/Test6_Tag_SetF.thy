(* Plan section 7 test 6 (plan lines 4663-4667), with K counted as in
   ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.6.  In the predicate-free SetF, inductive
   ipn in a nested context fixes A assumes hfin: "finite A" is stored as SetF.ipn.cases with K 0:
   no layer writes K, and the nested assumption is the rule's first own premise, as in stock.  In
   a reopened nested block of the same shape, with h: SetF.ipn n A a, "using hfin h proof (cases
   rule: SetF.ipn.cases)" gives the cases ipn_in / ipn_n -- the gate row; the unnamed "using hfin
   h proof cases" selects what the heavy twin SetF0 selects in the same blocks. *)
theory Test6_Tag_SetF
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale SetF0 = fixes n :: nat
context SetF0 begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
inductive ipn :: "nat \<Rightarrow> bool" where ipn_in: "x \<in> A \<Longrightarrow> ipn x" | ipn_n: "ipn n"
end
end
context SetF0 begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
ML \<open>
val heavy_unnamed =
  let val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>nat\<close>)] "h" "SetF0.ipn n A a"
  in case_names (run ctxt [@{thm hfin}, h] "cases" "W a") end;
\<close>
end
end

light_locale SetF = fixes n :: nat
context SetF begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
inductive ipn :: "nat \<Rightarrow> bool" where ipn_in: "x \<in> A \<Longrightarrow> ipn x" | ipn_n: "ipn n"
end
end

ML \<open>
val _ = \<^assert> (Setclass.count_of @{thm SetF.ipn.cases} = 0);
(* the stored proposition *)
val _ = \<^assert> (Thm.prop_of @{thm SetF.ipn.cases} aconv Logic.varify_global
  \<^prop>\<open>finite A \<Longrightarrow> SetF.ipn n A a \<Longrightarrow> (\<And>x. a = x \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> (a = n \<Longrightarrow> P) \<Longrightarrow> P\<close>);
\<close>

context SetF begin
context fixes A :: "nat set" assumes hfin: "finite A" begin
ML \<open>local
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>nat\<close>)] "h" "SetF.ipn n A a";
(* gate *)
val _ = \<^assert> (case_names (run ctxt [@{thm hfin}, h] "cases rule: SetF.ipn.cases" "W a") = ["ipn_in", "ipn_n"]);
(* the unnamed form, as the heavy twin's *)
val _ = \<^assert> (case_names (run ctxt [@{thm hfin}, h] "cases" "W a") = heavy_unnamed);
in end\<close>
end
end

end
