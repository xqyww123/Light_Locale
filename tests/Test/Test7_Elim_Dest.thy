(* Plan section 7 test 7, plan lines 4874-4889: [elim]/[dest] rules of a light block are directly
   usable (decision 9 (ii)).  Fixture: a leaf-local light locale LE and one hypothesis constant per
   row group, Rc0 .. Rc8, with the shared conclusion constant Sc: no rule concludes an Rc_i, so no
   rule of another group can close a row's goal (Rc3 never holds, so that the ex-falso rule bad6 is
   provable); the heavy twin is Test7_Elim_Dest_Heavy (its own leaf: the light rules are
   theory-global and would fire in a heavy block of this theory).  Most rules are proved in the
   rules block: a rule that carries its attribute at the lemma (bad5, bad6, badD, badE2, bad5',
   fooI) follows the control that its rows' goal is not closed before it, and bad and badE get
   [dest]/[elim] by declare in the rows block, right after the same kind of control; bad7 and the
   datatype's distinct rule are proved, with their apply safe rows, in the declaration block and
   have no control (Rc8, TA and TB occur in no other rule).  The rows of the rules block's rules
   run in a later reopened block, where the classical reasoner sees only the theory copy
   LE ?S ==> ... (their declaring block's local copy is the same as the heavy twin's and gets no
   row).  Rows: declare
   LE.bad [dest] -- blast closes the goal (control: not before); declare LE.badE [elim] -- blast
   ignores it (its conclusion is not a variable: ElimBadConcl), auto closes; bad5 [elim] (cases
   shape) -- blast and auto close; bad6 [elim] (ex falso) -- blast fails with "Ignoring weak
   elimination rule", auto closes; [dest!]/[elim!] -- by auto; apply safe with the safe rule bad7
   whose major premise does not bind ?S, and with a datatype's distinct rule -- the reopened block
   keeps a subgoal led by LE where the declaration block closes it; blast on the distinct rule's
   goal: "Ignoring weak elimination rule"; ".." with chained facts: bad5' [elim?] through
   from h LE_axioms (the derived rule's major premise first, LE ?S second; the other orders fail),
   fooI [intro] through from LE_axioms h .. and by (rule LE.fooI) (from h .. and the bare rule
   fail). *)
theory Test7_Elim_Dest
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

(*row groups: Rc0 bad, Rc1 badE, Rc2 bad5, Rc3 bad6, Rc4 badD, Rc5 badE2, Rc6 bad5', Rc7 fooI, Rc8 bad7*)
consts Sc :: 'a  Rc0 :: 'a  Rc1 :: 'a  Rc2 :: 'a  Rc3 :: 'a  Rc4 :: 'a  Rc5 :: 'a  Rc6 :: 'a  Rc7 :: 'a  Rc8 :: 'a
axiomatization where Sc_ax: "Sc x" and Rc3_ax: "Rc3 x (n :: nat) \<Longrightarrow> False"

ML \<open>
val light = Light_Locale_Axiom_Facts.is_light_prop;
(*after apply safe: the number of subgoals and whether the first is led by the light predicate*)
fun after_safe ctxt goal =
  let val st = run_apply ctxt [] "safe" goal
  in (subgoals st, subgoals st > 0 andalso light ctxt (Logic.strip_assums_concl (hd (goal_prems st)))) end;
\<close>

(* the declaration block holds the safe rules of the apply safe rows, and closes their goals *)
light_locale LE = fixes S :: nat assumes "S = S"
begin
lemma bad7 [elim!]: "Rc8 x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
datatype tr = TA | TB
ML_val \<open>
val _ = \<^assert> (after_safe \<^context> "Rc8 (a :: 'q) \<Longrightarrow> Sc a" = (0, false));
val _ = \<^assert> (after_safe \<^context> "TA = TB \<Longrightarrow> P" = (0, false));
\<close>
end

(* the rules block: a rule that carries its attribute at the lemma follows the control that its
   rows' goal is not closed before it; bad and badE get theirs by declare in the rows block *)
context LE begin
lemma bad: "Rc0 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma badE: "Rc1 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc2 (a :: 'q) S \<Longrightarrow> Sc a\<close>) andalso not (by_auto \<^context> \<^prop>\<open>Rc2 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
lemma bad5 [elim]: "Rc2 x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc3 (a :: 'q) S \<Longrightarrow> Q\<close>) andalso not (by_auto \<^context> \<^prop>\<open>Rc3 (a :: 'q) S \<Longrightarrow> Q\<close>))\<close>
lemma bad6 [elim]: "Rc3 x S \<Longrightarrow> R" by (drule Rc3_ax) simp
ML_val \<open>\<^assert> (not (by_auto \<^context> \<^prop>\<open>Rc4 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
lemma badD [dest!]: "Rc4 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML_val \<open>\<^assert> (not (by_auto \<^context> \<^prop>\<open>Rc5 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
lemma badE2 [elim!]: "Rc5 x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc6 a S";
val _ = \<^assert> (not (by_method ctxt [h, @{thm LE_axioms}] "standard" "Sc a"));
\<close>
lemma bad5' [elim?]: "Rc6 x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc7 a S";
val _ = \<^assert> (not (by_method ctxt [@{thm LE_axioms}, h] "standard" "Sc a"));
\<close>
lemma fooI [intro]: "Rc7 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

(* the rows, in a later reopened block: only the theory copies of the rules are visible *)
context LE begin
(*[dest] through declare; the control: not before*)
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc0 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
declare LE.bad [dest]
lemma "Rc0 (a :: 'q) S \<Longrightarrow> Sc a" by blast
(*[elim] through declare: blast ignores it (asserted under auto only); the control: not before*)
ML_val \<open>\<^assert> (not (by_auto \<^context> \<^prop>\<open>Rc1 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
declare LE.badE [elim]
lemma "Rc1 (a :: 'q) S \<Longrightarrow> Sc a" by auto
(*bad5 [elim]*)
lemma "Rc2 (a :: 'q) S \<Longrightarrow> Sc a" by blast
lemma "Rc2 (a :: 'q) S \<Longrightarrow> Sc a" by auto
(*bad6 [elim], ex falso: the theory copy LE ?S ==> Rc3 ?x ?S ==> ?R is a weak elimination rule
  for blast, which fails with the warning where the heavy twin's blast closes the goal; auto closes*)
ML_val \<open>\<^assert> (blast_warns \<^context> "Rc3 (a :: 'q) S \<Longrightarrow> Q" = (false, true))\<close>
lemma "Rc3 (a :: 'q) S \<Longrightarrow> Q" by auto
(*[dest!]/[elim!]*)
lemma "Rc4 (a :: 'q) S \<Longrightarrow> Sc a" by auto
lemma "Rc5 (a :: 'q) S \<Longrightarrow> Sc a" by auto
(*apply safe: the safe rules whose major premise does not bind ?S leave LE ?S first*)
ML_val \<open>
val _ = \<^assert> (after_safe \<^context> "Rc8 (a :: 'q) \<Longrightarrow> Sc a" = (1, true));
val _ = \<^assert> (after_safe \<^context> "TA = TB \<Longrightarrow> P" = (1, true));
val _ = \<^assert> (blast_warns \<^context> "TA = TB \<Longrightarrow> P" = (false, true));
\<close>
(*".." with chained facts (plan lines 4884-4889): the derived rule of bad5' has the major premise
  first and LE ?S second, so the chained facts must come in that order; the terminal step closes a
  subgoal only from its own premises, so "from h .." leaves LE S open and fails; fooI [intro] is
  reached by ".." and by (rule LE.fooI) with LE_axioms first, and neither the other order, nor h
  alone, nor the bare rule proves the goal*)
lemma assumes h: "Rc6 (a :: 'q) S" shows "Sc a" using h LE_axioms ..
lemma assumes h: "Rc7 (a :: 'q) S" shows "Sc a" using LE_axioms h ..
lemma assumes h: "Rc7 (a :: 'q) S" shows "Sc a" using LE_axioms h by (rule LE.fooI)
ML_val \<open>
val lf = @{thm LE_axioms};
val (h6, ctxt6) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc6 a S";
val (h7, ctxt7) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc7 a S";
val _ = \<^assert> (not (by_method ctxt6 [lf, h6] "standard" "Sc a"));
val _ = \<^assert> (not (by_method ctxt6 [h6] "standard" "Sc a"));
val _ = \<^assert> (not (by_method ctxt7 [h7, lf] "standard" "Sc a"));
val _ = \<^assert> (not (by_method ctxt7 [h7] "standard" "Sc a"));
val _ = \<^assert> (not (by_method ctxt7 [h7, lf] "rule LE.fooI" "Sc a"));
val _ = \<^assert> (not (by_method ctxt7 [] "rule LE.fooI" "Sc a"));
\<close>
end

end
