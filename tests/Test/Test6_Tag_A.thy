(* Plan section 7 test 6, redeclaring a tagged theorem adds no premise, leaf A (plan lines
   4647-4658): SetN.fooN, proved in a nested assumes block of the predicate-free SetN, is stored as
   0 < ?n ==> Qn ?n ==> Rn ?n & Rn' ?n with K 1; lemmas fooN1 [dest] = SetN.fooN in a reopened
   context SetN keeps K 1 and the statement, the derived dest rule's major premise is Qn ?n; in
   context LF, lemmas g = SetN.fooN[THEN conjunct1, exported_premises 1] and lemmas g2 =
   SetN.fooN[of y for y] keep K 1 without LF ?S, while the row-level "for" of lemmas g3 =
   SetN.fooN[of y] for y clears the tag before light_notes and the stock export adds LF ?S. *)
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
fun major_is c th =
  (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of th)) of
    (Const (c', _), args) => c' = c andalso forall is_Var args
  | _ => false);
fun no_LF th = not (exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of th));
\<close>

context SetN begin
lemmas fooN1 [dest] = SetN.fooN
end
ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm SetN.fooN1} = 1 andalso Thm.eq_thm_prop (@{thm SetN.fooN1}, @{thm SetN.fooN}));
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Qn\<close> plain) (claset_entries \<^context> @{thm SetN.fooN1}));
\<close>

context LF begin
lemmas g = SetN.fooN[THEN conjunct1, exported_premises 1]
lemmas g2 = SetN.fooN[of y for y]
lemmas g3 = SetN.fooN[of y] for y
end
ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.g} aconv Logic.varify_global \<^prop>\<open>0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g} = 1 andalso no_LF @{thm LF.g});
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g2} = 1 andalso no_LF @{thm LF.g2});
val _ = \<^assert> (Thm.prop_of @{thm LF.g3} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> 0 < y \<Longrightarrow> Qn y \<Longrightarrow> Rn y \<and> Rn' y\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.g3} = 1);
\<close>

end
