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
   declaration ends the leaf, so a test-first run must comment out rows
   1 and 5-8 (plan section 11 (39)).  The grouping is that of the rows as first written, when a
   light header could still declare G (structure) or R (structure) itself (rows 2-4, 8); now rows
   2, 4 and 8 inherit G from Gm and row 3 is built on UPr. *)
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
\<close>


subsection \<open>The rows that ran before the fix but gave the wrong result\<close>

(* row 2: Gm's G, after UP_cring S, is the first layer beside the cut UP S -- the attribute reads
   \<one> on UP S, as the body does; were G to beat the cut, on G; the twin's first layer is P *)
light_locale LFgat = UP_cring S + Gm for S +
  assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale Dgat = UP_cring S + Gm for S +
  assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFgat begin
ML \<open>val _ = \<^assert> (#1 (layers \<^context>) = SOME "G")\<close>
ML \<open>val _ = premises_are \<^context> @{thm LFgat.ax [OF LFgat_axioms]} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
context Dgat begin
ML \<open>val _ = premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML \<open>val _ = same_attribute_terms \<^theory> ("LFgat", "Dgat") ["P"]\<close>

(* row 3: UPr's P eliminated (the cut f R), its R kept as the first layer -- the attribute reads
   \<one> on f R; were R to beat the cut, on R; the twin's first layer is P *)
light_locale LRat = UPr + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale DRat = UPr + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LRat begin
ML \<open>val _ = \<^assert> (#1 (layers \<^context>) = SOME "R")\<close>
ML \<open>val _ = premises_are \<^context> @{thm LRat.ax [OF LRat_axioms]} 1 "\<one>\<^bsub>f R\<^esub> = \<one>\<^bsub>f R\<^esub>"\<close>
end
context DRat begin
ML \<open>val _ = premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML \<open>val _ = same_attribute_terms \<^theory> ("LRat", "DRat") ["P"]\<close>

(* row 4: a term parameter read once and a string parameter read again at the second
   evaluation, in the new locale's target: the same premise twice -- the declaration's value
   equals the one Locale.init computes; Gm's G is the first layer beside the cut UP S, and were G
   to beat the cut, a premise would be on G *)
light_locale LFbat = UP_cring S + Gm for S +
  assumes ax [t9_premise "\<one>", THEN t9_premise_rule[where x = "\<one>"]]: "\<one> \<otimes> \<one> = \<one>"
context LFbat begin
ML \<open>val _ = \<^assert> (#1 (layers \<^context>) = SOME "G")\<close>
ML \<open>val _ = premises_are \<^context> @{thm LFbat.ax [OF LFbat_axioms]} 2 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end

(* row 12: the activation context the declaration entry point returns (the heavy branch, a
   heavy header importing a light locale): with LF it holds UP S, the placeholder fixed; with
   Gm no second layer *)
ML \<open>local
val ctxt = activation_context (Proof_Context.init_global \<^theory>) "LF";
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S") andalso placeholder_fixed ctxt);
in end\<close>
ML \<open>val _ = \<^assert> (is_none (#2 (layers (activation_context (Proof_Context.init_global \<^theory>) "Gm"))))\<close>


subsection \<open>The rows the fix leaves unchanged\<close>

(* row 9: the walk gives names <> [], no second layer -- the attribute reads R, as the twin *)
light_locale LFr2at = UP_cring + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale DR2at = UP_cring + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFr2at begin
ML \<open>val _ = premises_are \<^context> @{thm LFr2at.ax [OF LFr2at_axioms]} 1 "\<one>\<^bsub>R\<^esub> = \<one>\<^bsub>R\<^esub>"\<close>
end
ML \<open>val _ = same_attribute_terms \<^theory> ("LFr2at", "DR2at") ["P"]\<close>

(* row 10: a heavy header without a light import reads the first layer's head; with no
   structure at all the bare index has nothing to denote *)
locale Gat = Gm + assumes ax [t9_premise "\<one>"]: "G = G"
context Gat begin
ML \<open>val _ = premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<^esub>"\<close>
end
ML \<open>
val _ = fails_checked "a message naming the implicit structure"
  (String.isSubstring "Illegal reference to implicit structure")
  (heavy \<^theory> "Zat = fixes c :: nat assumes h [t9_premise \"\<one>\"]: \"c = c\"")
\<close>

(* row 11: a nested context in a light block, no import: the outer second layer is read *)
context LF begin
context fixes c :: nat assumes h [t9_premise "\<one>"]: "c = c" begin
ML \<open>val _ = premises_are \<^context> @{thm h} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
end

(* row 13: from a context that already has a second layer (set directly: a block of LFr cannot
   declare LF, UP_ring's lcoeff would be declared twice) that layer stays -- the header's guard,
   not a recomputation *)
ML \<open>local
val ctxt0 = Proof_Context.init_global \<^theory>;
val ctxt = activation_context (Proof_Context.declare_implicit_structure (reads ctxt0 "tmk (0::nat)") ctxt0) "LF";
val _ = \<^assert> (implicit_is ctxt (reads ctxt "tmk (0::nat)"));
in end\<close>


subsection \<open>The rows whose declaration failed before the fix\<close>

(* row 1: the gate shape *)
light_locale LFat = UP_cring S for S + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale Dat = UP_cring S for S + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context LFat begin
ML \<open>val _ = premises_are \<^context> @{thm LFat.ax [OF LFat_axioms]} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
context Dat begin
ML \<open>val _ = premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>"\<close>
end
ML \<open>val _ = same_attribute_terms \<^theory> ("LFat", "Dat") ["P"]\<close>

(* row 5: the cut at the first import *)
locale Hs2at = bounded_linear f + LF for f + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
locale DHs2at = bounded_linear f + D for f + assumes ax [t9_premise "\<one>"]: "\<one> \<otimes> \<one> = \<one>"
context Hs2at begin
ML \<open>val _ = premises_are \<^context> @{thm ax} 1 "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>"\<close>
end
ML \<open>val _ = same_attribute_terms \<^theory> ("Hs2at", "DHs2at") ["P"]\<close>

(* row 6: a heavy header's notes element, read through Element.activate's Notes branch *)
locale HLn = LF + notes n = refl[of "\<one>"]
locale DLn = D + notes n = refl[of "\<one>"]
context HLn begin
ML \<open>val _ = \<^assert> (Thm.prop_of @{thm n} aconv Syntax.read_prop \<^context> "\<one>\<^bsub>UP S\<^esub> = \<one>\<^bsub>UP S\<^esub>")\<close>
end
context DLn begin
ML \<open>val _ = \<^assert> (Thm.prop_of @{thm n} aconv Syntax.read_prop \<^context> "\<one>\<^bsub>P\<^esub> = \<one>\<^bsub>P\<^esub>")\<close>
end

(* row 7: a value with a binder (LFl's S(|mult := \<lambda>x y. x|)): the terms, types included, equal
   the twin's after elimination *)
locale Hl4at = LFl + assumes ax [t9_premise "\<one>"]: "x \<otimes> \<one> = x"
locale DHl4at = Dl + assumes ax [t9_premise "\<one>"]: "x \<otimes> \<one> = x"
ML \<open>val _ = same_attribute_terms \<^theory> ("Hl4at", "DHl4at") ["M"]\<close>

(* row 8: a string parameter whose type constraint fits the second layer (nat \<Rightarrow> 'a) and not G
   (Gm's, the first layer): were G to beat the cut, the declaration would fail with a type error *)
light_locale LFwat = UP_cring S + Gm for S +
  assumes ax [THEN t9_premise_rule[where x = "\<one> :: nat \<Rightarrow> _"]]: "\<one> \<otimes> \<one> = \<one>"
context LFwat begin
ML \<open>val _ = \<^assert> (#1 (layers \<^context>) = SOME "G")\<close>
end

end
