(* Plan section 7 test 6, the rule-search priority row (plan lines 4498-4502): with a K 0 cases
   rule LF_cases [cases pred: LF] declared at theory level, "using LF_axioms h proof cases" in the
   reopened block selects LF_cases (the 0th chained fact LF_axioms selects K 0 rules), while
   "(cases rule: LF.ip.cases)" still gives ip's cases. *)
theory Test6_Cases_Priority
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

context LF begin
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end

lemma LF_cases [case_names lf, cases pred: LF]: "LF S \<Longrightarrow> (LF S \<Longrightarrow> W) \<Longrightarrow> W" by blast

ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm LF_cases} = 0);\<close>

context LF begin
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "h" "LF.ip S n";
val _ = \<^assert> (case_names (run ctxt [@{thm LF_axioms}, h] "cases" "W n") = ["lf"]);
val _ = \<^assert> (case_names (run ctxt [@{thm LF_axioms}, h] "cases rule: LF.ip.cases" "W n") = ["z", "s"]);
\<close>
end

end
