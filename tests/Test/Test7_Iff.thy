(* Plan section 7 test 7, plan lines 4905-4914: [iff] in a light block.  In LI's declaration block
   lemma biff [iff]: "Rc x S <-> Sc x" is the local copy, a safe iff rule as in the heavy block:
   simp, auto and blast close Rc c S ==> Sc c there, and ".." with the chained h: Sc x proves
   Rc x S (plan line 4915).  In a reopened block the theory copy
   LI ?S ==> (Rc ?x ?S <-> Sc ?x) is a simp rule (by simp, by auto) and its derived classical halves
   are in the unsafe tables: the intro half Sc ?x ==> LI ?S ==> Rc ?x ?S and the dest half
   Rc ?x ?S ==> LI ?S ==> Sc ?x, read back from Classical.dest_decls by the keys
   zero_var_indexes (rotate_prems 1 (LI.biff RS iffD2/iffD1)) (clasimp.ML:87-96), without tags;
   blast closes Rc c S ==> Sc c through the dest half and LI_axioms [intro!].  The ".." rows and
   their measured polarities are at the rows.  The heavy twin is Test7_Iff_Heavy, the downstream
   rows Test7_Iff_Downstream. *)
theory Test7_Iff
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Rc :: 'a  Sc :: 'a
axiomatization where RcSc_ax: "Rc x (n :: nat) \<longleftrightarrow> Sc x"

light_locale LI = fixes S :: nat assumes "S = S"
begin
lemma biff [iff]: "Rc x S \<longleftrightarrow> Sc x" by (rule RcSc_ax)
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by simp
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by auto
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by blast
lemma assumes h: "Sc (x :: 'q)" shows "Rc x S" using h ..
ML_val \<open>
(*the local copy: safe halves*)
val intro_key = zero_var_indexes (rotate_prems 1 (@{thm biff} RS @{thm iffD2}));
val _ = \<^assert> (exists (fn (_, _, k) => k = Bires.intro_bang_kind) (claset_entries \<^context> intro_key));
\<close>
end

context LI begin
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by simp
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by auto
lemma "Rc (c :: 'q) S \<Longrightarrow> Sc c" by blast
ML_val \<open>
val ctxt = \<^context>;
val intro_key = zero_var_indexes (rotate_prems 1 (@{thm LI.biff} RS @{thm iffD2}));
val dest_key = zero_var_indexes (rotate_prems 1 (@{thm LI.biff} RS @{thm iffD1}));
val (ikey, iplain) = claset_rule ctxt Bires.intro_kind intro_key;
val (dkey, _) = claset_rule ctxt Bires.dest_kind dest_key;
val _ = \<^assert> (Thm.prop_of iplain aconv Logic.varify_global \<^prop>\<open>Sc (x :: 'a) \<Longrightarrow> LI S \<Longrightarrow> Rc x S\<close>);
val _ = \<^assert> (null (Thm.get_tags ikey) andalso null (Thm.get_tags dkey));
(*the unsafe kinds are the only ones the halves are registered with (rev 18 registered the safe
  ones; a safe entry next to the unsafe one would make safe leave LI b downstream)*)
val _ = \<^assert> (map #3 (claset_entries ctxt intro_key) = [Bires.intro_kind]);
val _ = \<^assert> (map #3 (claset_entries ctxt dest_key) = [Bires.dest_kind]);
(*".." with chained facts (plan lines 4913-4914): from h LI_axioms closes the goal, the other orders do not*)
val (h, ctxt') = assume_in ctxt [("x", \<^typ>\<open>'q\<close>)] "h" "Sc x";
val lf = @{thm LI_axioms};
val _ = \<^assert> (by_method ctxt' [h, lf] "standard" "Rc x S");
val _ = \<^assert> (not (by_method ctxt' [lf, h] "standard" "Rc x S"));
val _ = \<^assert> (not (by_method ctxt' [h] "standard" "Rc x S"));
\<close>
end

end
