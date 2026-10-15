(* The heavy twin of Test7_Modifiers (plan lines 4902-4905), in its own theory: in the heavy block
   DM, auto dest: fooD closes the goal bare auto does not, erule fooE0 applies, erule ip.cases
   leaves the one subgoal x = 0 ==> x = 0 (the literal Test7_Modifiers compares with), subst fooS
   leaves one subgoal. *)
theory Test7_Modifiers_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Rd :: 'a  Sd :: 'a
axiomatization where Sd_ax: "Sd x" and RdSd_ax: "Rd x (n :: nat) = Sd x"

locale DM = fixes S :: nat assumes "S = S"

context DM begin
lemma fooD: "Rd x S \<Longrightarrow> Sd x" by (rule Sd_ax)
lemma fooE0: "Rd x S \<Longrightarrow> (Sd x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sd_ax)
lemma fooS: "Rd x S = Sd x" by (rule RdSd_ax)
inductive ip :: "nat \<Rightarrow> bool" where ip0: "ip 0"
ML_val \<open>
val ctxt = \<^context>;
val goal = "Rd (a :: 'q) S \<Longrightarrow> Sd a";
val _ = \<^assert> (not (by_method ctxt [] "auto" goal));
val _ = \<^assert> (by_method ctxt [] "auto dest: fooD" goal);
val _ = \<^assert> (by_method ctxt [] "erule fooE0" goal);
val _ = \<^assert> (eq_list (op aconv) (goal_prems (run_apply ctxt [] "erule ip.cases" "ip x \<Longrightarrow> x = 0"),
  [\<^prop>\<open>(x :: nat) = 0 \<Longrightarrow> x = 0\<close>]));
val _ = \<^assert> (subgoals (run_apply ctxt [] "subst fooS" "Rd (a :: 'q) S") = 1);
\<close>
end

end
