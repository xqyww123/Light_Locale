(* Plan section 7 test 6, the residual-parameter row (plan lines 4469-4471): LFu fixes S and T but
   its predicate mentions only S; a block inductive whose rule mentions T is stored as LFu.evu ?T ?a,
   ?T a variable that is not in the leading K premises.  In the reopened block, with h: LFu.evu T n,
   "using LFu_axioms h proof (cases n)" reads nat's case names (n goes to ?T's position),
   "(cases T n)" reads evu's. *)
theory Test6_Cases_Residual
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

light_locale LFu = fixes S :: "nat set" and T :: "nat set" assumes fu: "finite S"

context LFu begin
inductive evu :: "nat \<Rightarrow> bool" where "evu 0" | "evu n \<Longrightarrow> evu (Suc (Suc n))" | "Pc T (7::nat) \<Longrightarrow> evu 7"
end

ML \<open>
val _ = \<^assert> (Thm.prop_of (hd @{thms LFu.evu.intros}) aconv
  Logic.varify_global \<^prop>\<open>LFu S \<Longrightarrow> LFu.evu T 0\<close>);
\<close>

context LFu begin
ML \<open>local
val (h, ctxt) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "h" "LFu.evu T n";
val _ = \<^assert> (case_names (run ctxt [@{thm LFu_axioms}, h] "cases n" "W n") = ["0", "Suc"]);
val _ = \<^assert> (case_names (run ctxt [@{thm LFu_axioms}, h] "cases T n" "W n") = ["1", "2", "3"]);
in end\<close>
end

end
