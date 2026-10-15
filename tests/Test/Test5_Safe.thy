(* Plan section 7 test 5 (external use and propagation): LF_axioms fully activated through a heavy importer keeps [simp, intro!]: in context H begin (locale H = LF) safe closes the goal LF z, and after interpretation I: H t safe closes LF t at theory level. *)
theory Test5_Safe
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale T = fixes z :: nat assumes "z = z"
lemma (in T) tt: "z + 0 = z" by simp
abbreviation (in T) ta where "ta \<equiv> z + 1"
consts t :: nat
light_locale LF = T
locale H = LF

context H begin
ML_val \<open>\<^assert> (proves safe_tac \<^context> \<^prop>\<open>LF z\<close>)\<close>
end

interpretation I: H t by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (proves safe_tac ctxt \<^prop>\<open>LF t\<close>);
(*negative control: a predicate nobody declared [intro!] is not closed by safe*)
val _ = \<^assert> (not (proves safe_tac ctxt \<^prop>\<open>T (t + 5)\<close>));
\<close>

end
