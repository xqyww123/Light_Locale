(* Plan section 7 test 6, a heavy locale importing a light one (plan lines 4740-4749): locale H =
   LF + fixes z assumes hz.  In H's block the bare lemmas foo2 [case_names a b] = LF.foo puts case
   a on LF ?S (negative), the bare declare LF.foo [elim] registers a rule whose major premise is
   LF ?S (negative); foo2' [case_names a b] = LF.foo[OF LF_axioms] and declare LF.foo[OF LF_axioms,
   elim] agree with the heavy twin Hh's rows (up to K, K 0; the one elim entry: K 0 key, the same
   Rule_Cases, the same derived rule up to renaming); "using LF_axioms h proof cases" prints the
   twin's cases (pinned to ip's z / s), the bare "using h proof cases" falls to case_split; after
   interpretation I: H t 0 the same pair at theory level, the cases compared term by term with
   the twin's interpretation Ih (the instance names differ, LF.ip t against D.ip t: twin_names).
   The row of plan lines 4748-4749 is dropped (section 11, item (27)). *)
theory Test6_Heavy_Imports
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"
axiomatization t :: "nat ring" where t: "cring t"

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
fun major_light ctxt th = Light_Locale_Axiom_Facts.is_light_prop ctxt (Thm.major_prem_of th);
\<close>

context D begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end
context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end

locale Hh = D + fixes z :: nat assumes hz: "Qc z"
context Hh begin
lemmas foo2 [case_names a b] = foo
declare foo [elim]
ML \<open>
val heavy_foo2 = @{thm foo2};
val heavy_foo_elim = claset_rule \<^context> Bires.elim_kind @{thm foo};
val heavy_H_cases =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_text st end;
\<close>
end
interpretation Ih: Hh "UP t" t 0 by (rule Hh.intro) (rule D.intro, simp_all add: UP_cring_def t Hh_axioms_def Qc1_ax)
ML \<open>
val heavy_interp =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "D.ip t n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_terms canonical_vars st end;
\<close>

locale H = LF + fixes z :: nat assumes hz: "Qc z"
context H begin
lemmas foo2 [case_names a b] = LF.foo
ML_val \<open>
(* negative: case a lands on LF ?S *)
val (info, n) = Rule_Cases.get @{thm foo2};
val _ = \<^assert> (map (#1 o #1) info = ["a", "b"] andalso n = 0 andalso Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm foo2})));
\<close>
declare LF.foo [elim]
ML_val \<open>\<^assert> (major_light \<^context> (#2 (claset_rule \<^context> Bires.elim_kind @{thm LF.foo})))\<close>
lemmas foo2' [case_names a b] = LF.foo[OF LF_axioms]
declare LF.foo[OF LF_axioms, elim]
ML_val \<open>
val _ = \<^assert> (diff_K 0 (@{thm foo2'}, heavy_foo2));
val (key, plain) = claset_rule \<^context> Bires.elim_kind @{thm LF.foo [OF LF_axioms]};
val (hkey, hplain) = heavy_foo_elim;
val _ = \<^assert> (Exported_Premises.count_of key = 0 andalso diff_K 0 (key, hkey) andalso
  same_shape (Thm.prop_of plain, Thm.prop_of hplain));
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = \<^assert> (cases_text (run ctxt [@{thm LF_axioms}, h] "cases" "W n") = heavy_H_cases);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>
end

interpretation I: H t 0 by (simp add: H_def H_axioms_def LF_def UP_cring_def t Qc1_ax)
ML \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip t n";
val st = run ctxt [@{thm I.LF_axioms}, h] "cases" "W n";
(* the ?case binds say ?P against the twin's ?Pa (D fixes P): up to renaming *)
val _ = \<^assert> (cases_terms (canonical_vars o twin_names ("LF", "D")) st = heavy_interp);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>

end
