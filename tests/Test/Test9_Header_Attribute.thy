(* Plan section 7 test 9 (structure), the header rows with attributes (REV15-8, plan section 3.2
   item 3, section 11 (39)): the attribute arguments of a locale header's elements are read in the
   declaration's activation context, which holds the header's implicit structure as the body
   does.  A term parameter is read once and kept in its token (t9_premise); a string parameter is
   read again at the second evaluation, in the new locale's target (t9_premise_rule[where x =
   ...]); the two agree, and what the light locale records equals its heavy twin's after
   elimination (Test_Support's twin projection on the attribute terms).  The rows are those of
   the fix memo's table, ordered by what the unfixed tree did with them: first the rows that ran
   before the fix but gave the wrong result (2-4, 12), then the rows the fix leaves unchanged
   (9-11, 13), then the rows whose declaration failed (1, 5-8); on the unfixed tree a failing
   declaration hides every ML_val result of the leaf, so a test-first run must comment out rows
   1 and 5-8 (plan section 11 (39)). *)
theory Test9_Header_Attribute
  imports Test9_Fixtures "HOL.Real_Vector_Spaces"
begin

ML \<open>
open Test_Support;

(*the light locale's attribute terms equal its heavy twin's after elimination; a row whose
  elements record no attribute term would pass vacuously, so it is rejected first (one side
  suffices: eq_list makes the lengths agree)*)
fun same_attribute_terms thy (l, h) defined =
  if exists (null o #2) (attribute_terms thy (loc thy l))
  then error ("attribute rows: " ^ l ^ " records no attribute term")
  else if assumes_equal attribute_terms thy (loc thy l, loc thy h) defined then ()
  else error ("attribute rows: " ^ l ^ " differs from " ^ h ^ " after elimination");

(*the activation context the declaration entry point returns (the heavy branch)*)
fun activation_context ctxt name =
  #4 (#1 (Expression.read_declaration (locale_expression (Proof_Context.theory_of ctxt) name) I [] ctxt));

(*the fact's premises are n copies of the proposition read in the block, and the fact holds no
  placeholder; a light locale's block holds only the schematic theory copy of its assumption
  (decision 8), so the rows pin it to the block's parameters with [OF LF_axioms]*)
fun premises_are ctxt th n text =
  let val expected = Syntax.read_prop ctxt text; val prems = Thm.prems_of th in
    \<^assert> (length prems = n andalso forall (fn p => p aconv expected) prems andalso
      not (has_placeholder (Thm.prop_of th)))
  end;
\<close>


subsection \<open>The rows that ran before the fix but gave the wrong result\<close>

(* row 2: a (structure) fixes after the import -- the attribute read \<one> on G, the body on UP S;
   the twin's first layer is P *)
light_locale LFgat = UP_cring S for S + fixes G :: "('c, 'd) monoid_scheme" (structure)
  assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale Dgat = UP_cring S for S + fixes G :: "('c, 'd) monoid_scheme" (structure)
  assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFgat begin
ML_val \<open>premises_are \<^context> @{thm LFgat.ax [OF LFgat_axioms]} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
context Dgat begin
ML_val \<open>premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML_val \<open>same_attribute_terms \<^theory> ("LFgat", "Dgat") ["P"]\<close>

(* row 3: the import's R kept as a (structure) parameter -- the attribute read \<one> on R *)
light_locale LFrat = UP_cring R for R (structure) + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale Drat = UP_cring R for R (structure) + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFrat begin
ML_val \<open>premises_are \<^context> @{thm LFrat.ax [OF LFrat_axioms]} 1 "\<one>\<^bsub>UP R\<^esub> = \<one>\<^bsub>UP R\<^esub>"\<close>
end
context Drat begin
ML_val \<open>premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML_val \<open>same_attribute_terms \<^theory> ("LFrat", "Drat") ["P"]\<close>

(* row 4: a term parameter read once and a string parameter read again at the second
   evaluation, in the new locale's target: the same premise twice -- the declaration's value
   equals the one Locale.init computes *)
light_locale LFbat = UP_cring S for S + fixes G :: "('c, 'd) monoid_scheme" (structure)
  assumes ax [t9_premise "\<one>", THEN t9_premise_rule[where x = "\<one>"]]: "\<one> \<otimes> \<one> = \<one>"
context LFbat begin
ML_val \<open>premises_are \<^context> @{thm LFbat.ax [OF LFbat_axioms]} 2 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end

(* row 12: the activation context the declaration entry point returns (the heavy branch, a
   heavy header importing a light locale): with LF it holds UP S, the placeholder fixed; with
   Gm no second layer *)
ML_val \<open>
val ctxt = activation_context (Proof_Context.init_global \<^theory>) "LF";
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S") andalso placeholder_fixed ctxt);
\<close>
ML_val \<open>\<^assert> (is_none (#2 (layers (activation_context (Proof_Context.init_global \<^theory>) "Gm"))))\<close>


subsection \<open>The rows the fix leaves unchanged\<close>

(* row 9: the walk gives names <> [], no second layer -- the attribute reads R, as the twin *)
light_locale LFr2at = UP_cring + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale DR2at = UP_cring + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFr2at begin
ML_val \<open>premises_are \<^context> @{thm LFr2at.ax [OF LFr2at_axioms]} 1 "\<one>\<^bsub>R\<^esub> = \<one>\<^bsub>R\<^esub>"\<close>
end
ML_val \<open>same_attribute_terms \<^theory> ("LFr2at", "DR2at") ["P"]\<close>

(* row 10: a heavy header without a light import reads the first layer's head; with no
   structure at all the bare index has nothing to denote *)
locale Gat = Gm + assumes ax [t9_premise "\<one>"]: "G = G"
context Gat begin
ML_val \<open>premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<^esub>"\<close>
end
ML_val \<open>
fails_checked "a message naming the implicit structure"
  (String.isSubstring "Illegal reference to implicit structure")
  (heavy \<^theory> "Zat = fixes c :: nat assumes h [t9_premise \"\<one>\"]: \"c = c\"")
\<close>

(* row 11: a nested context in a light block, no import: the outer second layer is read *)
context LF begin
context fixes c :: nat assumes h [t9_premise "\<one>"]: "c = c" begin
ML_val \<open>premises_are \<^context> @{thm h} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
end

(* row 13: from a context that already has a second layer (set directly: a block of LFr cannot
   declare LF, UP_ring's lcoeff would be declared twice) that layer stays -- the header's guard,
   not a recomputation *)
ML_val \<open>
val ctxt0 = Proof_Context.init_global \<^theory>;
val ctxt = activation_context (Proof_Context.declare_implicit_structure (reads ctxt0 "tmk (0::nat)") ctxt0) "LF";
val _ = \<^assert> (implicit_is ctxt (reads ctxt "tmk (0::nat)"));
\<close>


subsection \<open>The rows whose declaration failed before the fix\<close>

(* row 1: the gate shape *)
light_locale LFat = UP_cring S for S + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale Dat = UP_cring S for S + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFat begin
ML_val \<open>premises_are \<^context> @{thm LFat.ax [OF LFat_axioms]} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
context Dat begin
ML_val \<open>premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML_val \<open>same_attribute_terms \<^theory> ("LFat", "Dat") ["P"]\<close>

(* row 5: the cut at the first import *)
locale Hs2at = bounded_linear f + LF for f + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale DHs2at = bounded_linear f + D for f + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context Hs2at begin
ML_val \<open>premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
ML_val \<open>same_attribute_terms \<^theory> ("Hs2at", "DHs2at") ["P"]\<close>

(* row 6: a heavy header's notes element, read through Element.activate's Notes branch *)
locale HLn = LF + notes n = refl[of "\<one>"]
locale DLn = D + notes n = refl[of "\<one>"]
context HLn begin
ML_val \<open>\<^assert> (Thm.prop_of @{thm n} aconv Syntax.read_prop \<^context> "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>")\<close>
end
context DLn begin
ML_val \<open>\<^assert> (Thm.prop_of @{thm n} aconv Syntax.read_prop \<^context> "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>")\<close>
end

(* row 7: a value with a binder (LFl's S(|mult := \<lambda>x y. x|)): the terms, types included, equal
   the twin's after elimination *)
locale Hl4at = LFl + assumes ax [t9_premise "\<one>"]: "x \<otimes> \<one> = x"
locale DHl4at = Dl + assumes ax [t9_premise "\<one>"]: "x \<otimes> \<one> = x"
ML_val \<open>same_attribute_terms \<^theory> ("Hl4at", "DHl4at") ["M"]\<close>

(* row 8: a string parameter whose type constraint fits the second layer (nat \<Rightarrow> 'a) and not G:
   the declaration succeeds; before the fix its first evaluation reported a type error *)
light_locale LFwat = UP_cring S for S + fixes G :: "('c, 'd) monoid_scheme" (structure)
  assumes ax [THEN t9_premise_rule[where x = "\<one> :: nat \<Rightarrow> _"]]: "\<one> \<otimes> \<one> = \<one>"

end
