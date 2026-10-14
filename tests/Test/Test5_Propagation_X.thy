(* Plan section 7 test 5 (external use and propagation): sublocale X <= LF t with a heavy X: in X's declaration block and in a reopened context X there is no short-name theorem of T, while LF_axioms and the syntax are present; and the fully activated LF_axioms keeps [simp, intro!] -- safe closes the goal LF (u + 2) inside context X (safe does not simplify, only a safe intro rule closes it). *)
theory Test5_Propagation_X
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale T = fixes z :: nat assumes "z = z"
lemma (in T) tt: "z + 0 = z" by simp
abbreviation (in T) ta where "ta \<equiv> z + 1"
consts t :: nat
light_locale LF = T
locale H = LF
locale X = fixes u :: nat assumes "u = u"
sublocale X \<subseteq> LF "u + 2" by unfold_locales simp

context X begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (visible_fact_names ctxt = ["local.LF_axioms", "local.T_axioms", "local.X_axioms"]);
val _ = \<^assert> (consts_named ctxt "ta" = ["Test5_Propagation_X.T.ta", "local.ta"]);
val _ = \<^assert> (can (fn () => Goal.prove ctxt [] [] \<^prop>\<open>LF (u + 2)\<close> (fn {context, ...} => safe_tac context)) ());
\<close>
end

end
