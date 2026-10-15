(* Plan section 7 test 7, plan lines 4916-4918: the negated [iff] in a light block.  In LN's
   declaration block lemma niff [iff]: "~ Rc x S" is the local copy, and simp, auto and blast
   close Rc a S ==> False there; in a reopened block the theory copy is a simp
   rule and its classical half, read back by the key zero_var_indexes (rotate_prems 1 (LN.niff RS
   notE)) -- Rc ?x ?S ==> LN ?S ==> ?R -- is in the unsafe elim table and registered with no other
   kind; by auto closes Rc a S ==> False; by blast fails on it with "Ignoring weak elimination
   rule" (plan line 4917).  The heavy twin is Test7_Niff_Heavy, the downstream row
   Test7_Niff_Downstream. *)
theory Test7_Niff
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Rc :: 'a
axiomatization where Rc_ax: "\<not> Rc x (n :: nat)"

light_locale LN = fixes S :: nat assumes "S = S"
begin
lemma niff [iff]: "\<not> Rc x S" by (rule Rc_ax)
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by simp
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by auto
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by blast
end

context LN begin
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by simp
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by auto
ML_val \<open>
val ctxt = \<^context>;
val elim_key = zero_var_indexes (rotate_prems 1 (@{thm LN.niff} RS @{thm notE}));
val (ekey, eplain) = claset_rule ctxt Bires.elim_kind elim_key;
val _ = \<^assert> (null (Thm.get_tags ekey));
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt (nth (Thm.prems_of eplain) 1));
(*the unsafe kind is the only one the half is registered with (as in Test7_Iff)*)
val _ = \<^assert> (map #3 (claset_entries ctxt elim_key) = [Bires.elim_kind]);
(*blast fails on it with "Ignoring weak elimination rule" (plan line 4917), where the heavy twin's
  blast succeeds*)
val _ = \<^assert> (blast_warns ctxt "Rc (a :: 'q) S \<Longrightarrow> False" = (false, true));
\<close>
end

end
