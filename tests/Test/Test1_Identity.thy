(* Plan section 7 test 1 (invariance), the milestone-1 leaves on a theory with no light locale:
   is_light_prop is false for every premise of every named theorem of HOL-Algebra (thousands of
   premises led by heavy locale predicates); every dependency edge has Locale.is_light false at both
   ends; ring_axioms carries neither [simp] nor [intro] (simp and safe do not close ring R in
   context ring); the mutual-recursion regression on a local copy of HOL/Induct/Common_Patterns'
   Evn/Odd fixture, asserted against the stock values measured on the stock copy 2026-10-13;
   context monoid rows (a bare \<otimes> lemma, a nested context assumes with the heavy parameter name), a
   class without (structure), and the vector_space block with sublocale module scale rewrites. *)
theory Test1_Identity
  imports Test_Support
    "HOL-Algebra.Galois_Connection" "HOL-Algebra.FiniteProduct" "HOL-Algebra.Sylow"
    "HOL-Algebra.Bij" "HOL-Algebra.Multiplicative_Group" "HOL-Algebra.Zassenhaus"
    "HOL-Algebra.Divisibility" "HOL-Algebra.IntRing" "HOL-Algebra.UnivPoly"
    "HOL-Algebra.Algebraic_Closure_Type" "HOL-Algebra.Algebra"
begin

ML \<open>
val thy = \<^theory>;
val ctxt = Proof_Context.init_global thy;
(*every named fact of the theory, HOL-Algebra's included (fact names carry the theory's base name)*)
val facts = Facts.dest_static false [] (Global_Theory.facts_of thy);
val _ = \<^assert> (length facts > 10000);
val _ = \<^assert> (exists (String.isPrefix "UnivPoly." o #1) facts);
val prems = maps (fn (_, ths) => maps Thm.prems_of ths) facts;
val _ = \<^assert> (length prems > 1000);
val _ = \<^assert> (not (exists (Light_Locale_Axiom_Facts.is_light_prop ctxt) prems));
val _ = \<^assert> (null (Light_Locale_Axiom_Facts.retrieve ctxt \<^prop>\<open>cring R\<close>));
val deps = Locale.dest_dependencies [] thy;
val _ = \<^assert> (length deps > 100);
val _ = \<^assert> (forall (fn {source, target, ...} => not (Locale.is_light thy source) andalso not (Locale.is_light thy target)) deps);
\<close>

context ring begin
ML_val \<open>
fun proves tac prop = can (fn () => Goal.prove \<^context> [] [] prop (fn {context, ...} => tac context)) ();
val _ = \<^assert> (not (proves (fn c => simp_tac c 1) \<^prop>\<open>ring R\<close>));
val _ = \<^assert> (not (proves safe_tac \<^prop>\<open>ring R\<close>));
\<close>
end

(* the mutual-recursion regression *)
inductive Evn :: "nat \<Rightarrow> bool" and Odd :: "nat \<Rightarrow> bool"
where
  zero: "Evn 0"
| succ_Evn: "Evn n \<Longrightarrow> Odd (Suc n)"
| succ_Odd: "Odd n \<Longrightarrow> Evn (Suc n)"

ML \<open>
(*the stock values: the stock copy, scratchpad/stk/Stk_Evn.thy, 2026-10-13*)
val (is, th) = Rule_Cases.strict_mutual_rule \<^context> @{thms Evn_Odd.inducts};
val _ = \<^assert> (is = [1, 1]);
val _ = \<^assert> (Rule_Cases.get th = ([(("zero", []), []), (("succ_Evn", []), []), (("succ_Odd", []), [])], 0));
val _ = \<^assert> (Thm.get_tags th =
  [("consumes", "0"), ("cases_hyp_names", ",;,;,"), ("case_names", "zero;succ_Evn;succ_Odd")]);
val _ = \<^assert> (Exported_Premises.count_of th = 0);
\<close>

lemma "Evn n \<Longrightarrow> n = n" and "Odd m \<Longrightarrow> m = m"
proof (induct rule: Evn_Odd.inducts)
  ML_val \<open>\<^assert> (map #1 (Proof_Context.dest_cases NONE \<^context>) = ["zero", "succ_Evn", "succ_Odd"])\<close>
qed simp_all

(* heavy blocks with (structure) parameters still parse: a bare \<otimes>, a nested assumes naming the
   heavy parameter *)
context monoid begin
lemma t1_bare: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x" by simp
context assumes t1_h: "carrier G = carrier G" begin
lemma t1_nested: "\<one> \<in> carrier G" by simp
end
end

class C2 = ord + assumes c2: "x \<le> x"
ML \<open>
val _ = \<^assert> (can (Proof_Context.get_thm (Proof_Context.init_global \<^theory>)) "C2_axioms");
val _ = \<^assert> (not (Locale.is_light \<^theory> (Locale.check_global \<^theory> ("C2", Position.none))));
\<close>

(* the vector_space block with sublocale Modules.module scale rewrites "module_hom = linear" is not
   repeated here: after Real_Vector_Spaces is loaded, `linear` resolves to the global constant and
   stock itself cannot re-run that rewrites clause (a stock limitation, noted in the handoff) *)

end
