(* Plan section 7 test 7: the defines assumption of a nested block is unfolded by the stock export
   and is not counted by K: the defines layer keeps K (Local_Defs.def_export,
   ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.3).  The rows that pin it are fresh
   lemmas: in the predicate-free Setting, lemma t inside context fixes f defines "f == n + 1"
   stores PROP ?V ==> PROP ?W ==> PROP ?W with no K (no layer writes K; an assumption count
   would give 1); in the gate fixture LF, lemma t3 inside context fixes g defines "g == Suc 0"
   stores LF ?S ==> ?a == ?b ==> ?a = ?b with K 1, written by the light locale's layer (an
   assumption count would give the in-range K 2).  The redeclaration row of the flip table:
   lemmas t2 = v (v a theory fact with the vacuous premise a == b) in LF's defines layer stores v
   itself, count_of 0 (second version: a redeclaration of a fact unrelated to the block is stored
   as the theorem itself).  At the end the row N26: a defines layer whose definiendum is a prop
   occurring in a leading premise. *)
theory Test7_Defines_K
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale Setting = fixes n :: nat

context Setting begin
context fixes f :: nat defines "f \<equiv> n + 1" begin
lemma t: "PROP V \<Longrightarrow> PROP W \<Longrightarrow> PROP W" by assumption
end
end

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm Setting.t} aconv Thm.prop_of @{thm thin_rl});
val _ = \<^assert> (not (has_K_tag @{thm Setting.t}) andalso Thm.nprems_of @{thm Setting.t} = 2);
\<close>

(* plan line 4873: the predicate-free Setting declared and has no Setting_axioms, where the gate
   fixture's block has its LF_axioms (the control) *)
context Setting begin
ML \<open>val _ = \<^assert> (not (has_fact \<^context> "Setting_axioms"))\<close>
end
context LF begin
ML \<open>val _ = \<^assert> (has_fact \<^context> "LF_axioms")\<close>
end

lemma v: "(a::nat) \<equiv> b \<Longrightarrow> a = b" by simp

context LF begin
context fixes g :: nat defines "g \<equiv> Suc 0" begin
lemmas t2 = v
lemma t3: "(a::nat) \<equiv> b \<Longrightarrow> a = b" by simp
end
end

ML \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.t2}, @{thm v}) andalso not (has_K_tag @{thm LF.t2}));
val _ = \<^assert> (Thm.nprems_of @{thm LF.t2} = 1);
\<close>
ML \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.t3},
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (a::nat) \<equiv> b \<Longrightarrow> a = b\<close>));
val _ = \<^assert> (Setclass.count_of @{thm LF.t3} = 1 andalso Thm.nprems_of @{thm LF.t3} = 2);
\<close>

(* N26 (plan section 3.5 (b)).  The definiendum x is a prop occurring in the leading premise:
   def_export unfolds it to A ==> B and the normalisation splits A off as a premise of its own, at
   the end; the defines layer keeps K.  The local copy PROP x ==> PROP x with K 1; the theory copy
   (?A ==> ?B) ==> ?A ==> ?B with K 1 too (before the setclass batch the export's one shift counted
   the split-off premise into K, K 2). *)
context fixes A B :: bool and x :: "prop" defines x_def: "x \<equiv> (A \<Longrightarrow> B)" begin
lemma r26_0: "PROP x \<Longrightarrow> PROP x" .
lemmas r26 = r26_0 [setclass 1]
ML \<open>val _ = \<^assert> (Setclass.count_of @{thm r26} = 1 andalso Thm.nprems_of @{thm r26} = 1 andalso
  Thm.prop_of @{thm r26} aconv \<^prop>\<open>PROP x \<Longrightarrow> PROP x\<close>)\<close>
end
ML \<open>val _ = \<^assert> (Setclass.count_of @{thm r26} = 1 andalso Thm.nprems_of @{thm r26} = 2 andalso
  same_shape (Thm.prop_of @{thm r26}, Logic.varify_global \<^prop>\<open>(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close>))\<close>

end
