(* Plan section 7 test 5 (external use and propagation), plan lines 4206-4209: sublocale X <= LF t
   with a heavy X, declared inside X's block.  In the rest of that block and in a reopened context X
   there is no short-name theorem of T and no `ax` (LF's own head assumption: decision 8), while
   LF_axioms and the syntax are present; the fully activated LF_axioms keeps [simp, intro!] -- safe
   closes the goal LF (u + 2) (safe does not simplify, only a safe intro rule closes it).  LF.ax
   exists at theory level (the positive control for the absence of `ax`). *)
theory Test5_Propagation_X
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale T = fixes z :: nat assumes "z = z"
lemma (in T) tt: "z + 0 = z" by simp
abbreviation (in T) ta where "ta \<equiv> z + 1"
consts t :: nat
light_locale LF = T + assumes ax: "z = z"
locale H = LF

ML \<open>
val _ = \<^assert> (has_fact (Proof_Context.init_global \<^theory>) "LF.ax");
fun check ctxt =
  let
    val _ = \<^assert> (visible_fact_names ctxt = ["local.LF_axioms", "local.T_axioms", "local.X_axioms"]);
    val _ = \<^assert> (consts_named ctxt "ta" = ["Test5_Propagation_X.T.ta", "local.ta"]);
    val _ = \<^assert> (proves safe_tac ctxt \<^prop>\<open>LF (u + 2)\<close>);
  in () end;
\<close>

locale X = fixes u :: nat assumes "u = u"
begin
sublocale LF "u + 2" by unfold_locales simp
ML \<open>val _ = check \<^context>\<close>
end

context X begin
ML \<open>val _ = check \<^context>\<close>
end

end
