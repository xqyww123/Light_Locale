(* The heavy twin of Test7_Iff (plan lines 4905-4916), in its own theory: in the heavy block DI,
   biff [iff] is a safe iff rule; simp, auto and blast close Rc c S ==> Sc c, and the unchained
   from h show "Rc x S" .. succeeds; the theory-level copy registers nothing (section 5.7).  The
   theory-level row is the heavy side of Test7_Iff_Downstream: on its goal, apply safe leaves one
   subgoal and by auto succeeds. *)
theory Test7_Iff_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Rc :: 'a  Sc :: 'a
axiomatization where RcSc_ax: "Rc x (n :: nat) \<longleftrightarrow> Sc x"

locale DI = fixes S :: nat assumes "S = S"

context DI begin
lemma biff [iff]: "Rc x S \<longleftrightarrow> Sc x" by (rule RcSc_ax)
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by simp
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by auto
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by blast
lemma assumes h: "Sc (x :: 'q)" shows "Rc x S" using h ..
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val intro_key = zero_var_indexes (rotate_prems 1 (@{thm DI.biff} RS @{thm iffD2}));
val _ = \<^assert> (null (claset_entries ctxt intro_key));
(*the downstream goal of Test7_Iff_Downstream*)
val goal = "Rc (a :: 'q) (b :: nat) \<Longrightarrow> (\<exists>x. \<forall>y. R x y) \<Longrightarrow> \<forall>y. \<exists>x. R x y";
val _ = \<^assert> (subgoals (run_apply ctxt [] "safe" goal) = 1);
val _ = \<^assert> (by_method ctxt [] "auto" goal);
\<close>

end
