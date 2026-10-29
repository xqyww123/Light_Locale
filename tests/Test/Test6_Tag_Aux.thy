(* Plan section 7 test 6 (plan lines 4661-4662): a rule attribute that uses a block fact -- aux,
   proved in the reopened block, is stored the stock way and its local copy re-imports the block's
   assumption as a hyp whatever the proof used; lemmas xt = LF.foo[THEN aux] therefore carries the
   hyp, is exported the stock way and has two LF premises with K 1; lemmas xp = LF.foo[OF
   LF_axioms, THEN aux] has exactly one LF premise with K 1. *)
theory Test6_Tag_Aux
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
end

context LF begin
lemma aux: "A \<and> B \<Longrightarrow> B \<and> A" by (rule conj_commute [THEN iffD1])
lemmas xt = LF.foo[THEN aux]
lemmas xp = LF.foo[OF LF_axioms, THEN aux]
end

ML \<open>
val _ = \<^assert> (length (light_prems \<^context> @{thm LF.xt}) = 2 andalso Setclass.count_of @{thm LF.xt} = 1);
val _ = \<^assert> (length (light_prems \<^context> @{thm LF.xp}) = 1 andalso Setclass.count_of @{thm LF.xp} = 1);
\<close>

end
