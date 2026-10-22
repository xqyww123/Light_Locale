(* Plan section 7 test 6, redeclaring a tagged theorem adds no premise, leaf A (plan lines
   4647-4660): SetN.fooN, proved in a nested assumes block of the predicate-free SetN, is stored as
   0 < ?n ==> Qn ?n ==> Rn ?n & Rn' ?n with K 1; lemmas fooN1 [dest] = SetN.fooN in a reopened
   context SetN keeps K 1 and the statement, the derived dest rule's major premise is Qn ?n; lemmas
   fooN3 [dest] = SetN.fooN[of y] for y there keeps K 1 too (second version: the row-level for's
   Variable.export keeps K) and the derived dest rule's major premise is Qn ?y -- its
   proposition differs from fooN1's only in the variable names, which Classical's table tells apart
   (section 11, item (23)); in context LF, lemmas g = SetN.fooN[THEN conjunct1, exported_premises
   1] and lemmas g2 = SetN.fooN[of y for y] keep K 1 without LF ?S, and so does the row-level
   "for" of lemmas g3 = SetN.fooN[of y] for y: a redeclaration whose export changes nothing is
   stored as the theorem itself, 0 < ?y ==> Qn ?y ==> Rn ?y & Rn' ?y with K 1 and no LF ?S. *)
theory Test6_Tag_A
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Qn :: "nat \<Rightarrow> bool"  Rn :: "nat \<Rightarrow> bool"  Rn' :: "nat \<Rightarrow> bool"
axiomatization where qr: "0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n \<and> Rn' n"

light_locale SetN = fixes n :: nat
context SetN begin
context assumes hn: "0 < n" begin
lemma fooN: "Qn n \<Longrightarrow> Rn n \<and> Rn' n" by (rule qr[OF hn])
end
end

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm SetN.fooN} aconv
  Logic.varify_global \<^prop>\<open>0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n \<and> Rn' n\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm SetN.fooN} = 1);
\<close>

context SetN begin
lemmas fooN1 [dest] = SetN.fooN
end
ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm SetN.fooN1} = 1 andalso Thm.eq_thm_prop (@{thm SetN.fooN1}, @{thm SetN.fooN}));
val _ = \<^assert> (major_prem_is \<^context> "Qn (n :: nat)" (#2 (claset_rule \<^context> Bires.dest_kind @{thm SetN.fooN1})));
\<close>

context SetN begin
lemmas fooN3 [dest] = SetN.fooN[of y] for y
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm SetN.fooN3} = 1)\<close>
ML_val \<open>\<^assert> (major_prem_is \<^context> "Qn (y :: nat)" (#2 (claset_rule \<^context> Bires.dest_kind @{thm SetN.fooN3})))\<close>

context LF begin
lemmas g = SetN.fooN[THEN conjunct1, exported_premises 1]
lemmas g2 = SetN.fooN[of y for y]
lemmas g3 = SetN.fooN[of y] for y
end
ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.g} aconv Logic.varify_global \<^prop>\<open>0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g} = 1 andalso null (light_prems \<^context> @{thm LF.g}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g2} = 1 andalso null (light_prems \<^context> @{thm LF.g2}));
\<close>
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.g3},
  Logic.varify_global \<^prop>\<open>0 < y \<Longrightarrow> Qn y \<Longrightarrow> Rn y \<and> Rn' y\<close>));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g3} = 1 andalso null (light_prems \<^context> @{thm LF.g3}));
\<close>

end
