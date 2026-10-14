(* Plan section 7 test 7: the defines assumption of a nested block is unfolded by the stock export and is not counted by K: in the predicate-free Setting, lemmas t = thin_rl inside context fixes f defines "f == n + 1" stores PROP ?V ==> PROP ?W ==> PROP ?W with count_of 0; in the gate fixture LF, lemmas t2 = v (v a theory fact with the vacuous premise a == b) inside context fixes g defines "g == Suc 0" stores LF ?S ==> ?a == ?b ==> ?a = ?b, count_of 1. *)
theory Test7_Defines_K
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale Setting = fixes n :: nat

context Setting begin
context fixes f :: nat defines "f \<equiv> n + 1" begin
lemmas t = thin_rl
end
end

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm Setting.t} aconv Thm.prop_of @{thm thin_rl});
val _ = \<^assert> (Exported_Premises.count_of @{thm Setting.t} = 0);
\<close>

lemma v: "(a::nat) \<equiv> b \<Longrightarrow> a = b" by simp

context LF begin
context fixes g :: nat defines "g \<equiv> Suc 0" begin
lemmas t2 = v
end
end

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.t2} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (a::nat) \<equiv> b \<Longrightarrow> a = b\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.t2} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF.t2} = 2);
\<close>

end
