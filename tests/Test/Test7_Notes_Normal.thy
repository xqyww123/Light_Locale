(* Plan section 7 test 7, the head step of light_notes (section 11, item (14)): every input is
   normalised before the attributes see it, and its setclass count K survives the
   normalisation.  Row 1: lemmas lines whose rule attribute renumbers the variables ([where x = 1];
   [THEN conjunct1, setclass 1]) keep K = 1 on the theory copy -- Goal.norm_result keeps K
   itself (second version) and clears the other tags when it renumbers.  Row 2: a lemma whose attribute output is not in HHF form
   ([folded atomize_all] leaves an outer meta-all) is accepted, because the export callback
   normalises again before thm_definition. *)
theory Test7_Notes_Normal
  imports Test_Support
begin

light_locale LN = fixes n :: nat assumes ln: "0 < n"

lemma (in LN) lnp: "x = x \<and> n = n" for x :: nat by simp

context LN begin

lemmas lnw = LN.lnp[where x = 1]
lemmas lnt = LN.lnp[THEN conjunct1, setclass 1]

lemma lnf [folded atomize_all]: "\<forall>x::nat. x + n = n + x" by simp

end

ML \<open>
val _ = \<^assert> (Setclass.count_of @{thm LN.lnp} = 1);
val _ = \<^assert> (Setclass.count_of @{thm LN.lnw} = 1);
val _ = \<^assert> (Thm.prop_of @{thm LN.lnw} aconv
  Logic.varify_global \<^prop>\<open>LN n \<Longrightarrow> (1::nat) = 1 \<and> n = n\<close>);
val _ = \<^assert> (Setclass.count_of @{thm LN.lnt} = 1);
val _ = \<^assert> (Thm.prop_of @{thm LN.lnt} aconv
  Logic.varify_global \<^prop>\<open>LN n \<Longrightarrow> (x::nat) = x\<close>);
val _ = \<^assert> (Setclass.count_of @{thm LN.lnf} = 1);
val _ = \<^assert> (Thm.prop_of @{thm LN.lnf} aconv
  Logic.varify_global \<^prop>\<open>LN n \<Longrightarrow> (x::nat) + n = n + x\<close>);
\<close>

end
