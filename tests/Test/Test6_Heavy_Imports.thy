(* Plan section 7 test 6, a heavy locale importing a light one (plan lines 4740-4747): locale H =
   LF + fixes z assumes hz.  In H's block the bare lemmas foo2 [case_names a b] = LF.foo puts case
   a on LF ?S (negative), the bare declare LF.foo [elim] registers a rule whose major premise is
   LF ?S (negative); foo2' [case_names a b] = LF.foo[OF LF_axioms] and declare LF.foo[OF LF_axioms,
   elim] agree with the heavy twin Hh's rows (up to K, K 0; the same derived elim rule); "using
   LF_axioms h proof cases" prints the twin's cases, the bare "using h proof cases" falls to
   case_split; after interpretation I: H t 0 the same pair at theory level, compared by case names
   and assumption counts with the twin's interpretation Ih. *)
theory Test6_Heavy_Imports
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"
axiomatization t :: "nat ring" where t: "cring t"

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
fun run ctxt facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
val texts = Unsynchronized.ref (Symtab.empty: string list Symtab.table);
fun row name st = texts := Symtab.update (name, cases_text st) (! texts);
fun same (a, b) = Symtab.lookup (! texts) a = Symtab.lookup (! texts) b andalso is_some (Symtab.lookup (! texts) a);
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
ML \<open>val heavy_foo2 = @{thm foo2}; val heavy_foo_elim = map #2 (claset_entries \<^context> @{thm foo});\<close>
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
val _ = row "heavy H cases" (run ctxt [h] "cases" "W n");
\<close>
end
interpretation Ih: Hh "UP t" t 0 by (rule Hh.intro) (rule D.intro, simp_all add: UP_cring_def t Hh_axioms_def Qc1_ax)
ML \<open>
fun counts st = map (fn (_, Rule_Cases.Case {assumes, ...}) => length (maps #2 assumes)) (Proof_Context.dest_cases NONE (Proof.context_of st));
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "D.ip t n";
val heavy_interp = (fn st => (case_names st, counts st)) (run ctxt [h] "cases" "W n");
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
ML_val \<open>\<^assert> (exists (fn (_, plain, _) => major_light \<^context> plain) (claset_entries \<^context> @{thm LF.foo}))\<close>
lemmas foo2' [case_names a b] = LF.foo[OF LF_axioms]
declare LF.foo[OF LF_axioms, elim]
ML_val \<open>
val _ = \<^assert> (diff_K (@{thm foo2'}, heavy_foo2) andalso Exported_Premises.count_of @{thm foo2'} = 0);
val plains = map #2 (claset_entries \<^context> @{thm LF.foo [OF LF_axioms]});
val _ = \<^assert> (exists (fn p => exists (fn hp => same_shape (Thm.prop_of p, Thm.prop_of hp)) heavy_foo_elim) plains);
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = row "light H cases" (run ctxt [@{thm LF_axioms}, h] "cases" "W n");
val _ = \<^assert> (same ("light H cases", "heavy H cases"));
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>
end

interpretation I: H t 0 by (simp add: H_def H_axioms_def LF_def UP_cring_def t Qc1_ax)
ML \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip t n";
(* the theory-level pair: compared by case names and assumption counts (the printed text names
   the instance, LF.ip t against D.ip t) *)
val st = run ctxt [@{thm I.LF_axioms}, h] "cases" "W n";
val _ = \<^assert> ((case_names st, counts st) = heavy_interp);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>

end
