(* Plan section 7 test 9 (structure): the header route (plan section 3.2 item 6; rows at plan
   5178-5200, 5232-5250).  A light header's body reads bare index positions as the cut of its
   imports; what it records equals its heavy twin's assumptions after elimination (the twin's
   defined parameter replaced by its definition).  The three literal settings, mixed sorts, the
   import at index 1, the placeholder's type (the declared term with a binder is
   Test9_Header_Implicit row 21), the instances read before the body. *)
theory Test9_Header
  imports Test9_Fixtures "HOL.Real_Vector_Spaces"
begin

ML \<open>
open Test_Support;
\<close>


subsection \<open>The three literal settings of plan 5178-5180\<close>

light_locale LFa = UP_cring S for S + assumes ax: "x \<otimes> y = y \<otimes> x"
locale Da = UP_cring S for S + assumes ax: "x \<otimes> y = y \<otimes> x"
light_locale LFb = LF + assumes ax: "x \<otimes> y = y \<otimes> x"
locale Db = D + assumes ax: "x \<otimes> y = y \<otimes> x"
locale HLc = LF + assumes ax: "x \<otimes> y = y \<otimes> x"
locale DLc = D + assumes ax: "x \<otimes> y = y \<otimes> x"

ML \<open>
val thy = \<^theory>;
val _ = List.app (fn pair => same_as_twin thy pair ["P"]) [("LFa", "Da"), ("LFb", "Db"), ("HLc", "DLc")];
val _ = List.app (fn name =>
    \<^assert> (first_assumption thy name aconv
      Syntax.read_prop (Locale.init (loc thy name) thy)
        "\<And>x y. x \<otimes>\<^bsub>UP S\<^esub> y = y \<otimes>\<^bsub>UP S\<^esub> x"))
  ["LFa", "LFb", "HLc"];
\<close>


subsection \<open>The gate row and the three header-and-body rows (plan 5178-5187)\<close>

light_locale LFg = UP_cring S + Gm for S + assumes g: "x \<otimes> y = y \<otimes> x"
locale Dg = UP_cring S + Gm for S + assumes g: "x \<otimes> y = y \<otimes> x"

light_locale LFr2' = UP_cring + assumes "x \<otimes> y = y \<otimes> x"
locale DR2' = UP_cring + assumes "x \<otimes> y = y \<otimes> x"

locale HA = A + LF + assumes "x \<otimes> y = y \<otimes> x"
locale DHA = A + D + assumes "x \<otimes> y = y \<otimes> x"

locale DR2 = UP_cring
locale XH = LFr2 S for S + assumes "x \<otimes> y = y \<otimes> x"
locale DXH = DR2 S for S + assumes "x \<otimes> y = y \<otimes> x"

ML \<open>
val thy = \<^theory>;
val ctxt = Locale.init (loc thy "LFg") thy;
(*Gm's G, after UP_cring S, is the first layer beside the cut UP S*)
val _ = \<^assert> (#1 (layers ctxt) = SOME "G");
(*the body's bare operator is UP S's; were G to beat the cut, it would be G's*)
val _ = \<^assert> (first_assumption thy "LFg" aconv
  Syntax.read_prop ctxt "\<And>x y. x \<otimes>\<^bsub>UP S\<^esub> y = y \<otimes>\<^bsub>UP S\<^esub> x");
val _ = same_as_twin thy ("LFg", "Dg") ["P"];
(*LFr2': R survives, the walk gives names <> [], the body reads the first layer*)
val _ = same_as_twin thy ("LFr2'", "DR2'") ["P"];
val _ = \<^assert> (first_assumption thy "LFr2'" aconv
  Syntax.read_prop (Locale.init (loc thy "LFr2'") thy) "\<And>x y. x \<otimes>\<^bsub>R\<^esub> y = y \<otimes>\<^bsub>R\<^esub> x");
(*HA: A's G is first*)
val _ = same_as_twin thy ("HA", "DHA") ["P"];
val _ = \<^assert> (first_assumption thy "HA" aconv
  Syntax.read_prop (Locale.init (loc thy "HA") thy) "\<And>x y. x \<otimes>\<^bsub>G\<^esub> y = y \<otimes>\<^bsub>G\<^esub> x");
(*XH: the inherited cut UP R of LFr2, carried over the edge as UP S*)
val _ = same_as_twin thy ("XH", "DXH") ["P"];
val ctxt = Locale.init (loc thy "XH") thy;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S"));
val _ = \<^assert> (first_assumption thy "XH" aconv
  Syntax.read_prop ctxt "\<And>x y. x \<otimes>\<^bsub>UP S\<^esub> y = y \<otimes>\<^bsub>UP S\<^esub> x");
\<close>


subsection \<open>Mixed sorts and the import at index 1 (plan 5187-5199)\<close>

locale Hs = LF + bounded_linear f for f
locale DHs = D + bounded_linear f for f
locale Hs' = LF + bounded_linear f for f + assumes "x \<otimes> y = y \<otimes> x"
locale DHs' = D + bounded_linear f for f + assumes "x \<otimes> y = y \<otimes> x"
locale Hs2 = bounded_linear f + LF for f + assumes "x \<otimes> y = y \<otimes> x"
locale DHs2 = bounded_linear f + D for f + assumes "x \<otimes> y = y \<otimes> x"

ML \<open>
val thy = \<^theory>;
(*Hs has no body: same_as_twin compares two empty lists, only same_params carries information*)
val _ = same_params thy ("Hs", "DHs") ["P"];
val _ = same_as_twin thy ("Hs", "DHs") ["P"];
val _ = same_params thy ("Hs'", "DHs'") ["P"];
val _ = same_as_twin thy ("Hs'", "DHs'") ["P"];
val _ = same_as_twin thy ("Hs2", "DHs2") ["P"];
val ctxt = Locale.init (loc thy "Hs2") thy;
val _ = \<^assert> (first_assumption thy "Hs2" aconv
  Syntax.read_prop ctxt "\<And>x y. x \<otimes>\<^bsub>UP S\<^esub> y = y \<otimes>\<^bsub>UP S\<^esub> x");
(*the theory-level interpretation of the mixed-sort expression reaches its obligations*)
val _ = \<^assert> (can (fn () =>
  Named_Target.theory_init thy
  |> Interpretation.isar_interpretation_cmd (locale_expression thy "LF c + bounded_linear g")) ());
\<close>


subsection \<open>The placeholder's type: an expansion with a binder (plan 5234-5250)\<close>

(* UPl, LFl and Dl are in Test9_Fixtures *)
locale Hl1 = LFl + fixes z :: 'a assumes "x \<otimes> y = x"
locale DHl1 = Dl + fixes z :: 'a assumes "x \<otimes> y = x"
locale Hl2 = LFl + fixes w :: 'b assumes "x \<otimes> y = x"
locale DHl2 = Dl + fixes w :: 'b assumes "x \<otimes> y = x"
locale Hl3 = LFl + fixes z :: 'a assumes "x \<otimes> y = z"
locale DHl3 = Dl + fixes z :: 'a assumes "x \<otimes> y = z"

ML \<open>
val thy = \<^theory>;
val _ = List.app (fn pair => (same_params thy pair ["M"]; same_as_twin thy pair ["M"]))
  [("Hl1", "DHl1"), ("Hl2", "DHl2"), ("Hl3", "DHl3")];
(*the body's type variable and the element type are two type variables (plan 5241-5243)*)
val _ = \<^assert> (length (distinct (op =) (maps (fn (_, T, _) => Term.add_tfreesT T []) (params thy (loc thy "Hl1")))) = 3);

(*opening: the bare operator's type is the twin block's after elimination (the substitution maps
  M to a term of M's type, so it cannot change the type; it is kept because plan 5245-5246 says
  "after elimination")*)
fun bare_type name = fastype_of (reads (Locale.init (loc thy name) thy) "x \<otimes> y");
fun twin_type name =
  fastype_of (after_elimination thy name ["M"] (reads (Locale.init (loc thy name) thy) "x \<otimes> y"));
val _ = \<^assert> (bare_type "Hl1" = twin_type "DHl1");
val _ = \<^assert> (bare_type "Hl2" = twin_type "DHl2");
val _ = \<^assert> (bare_type "LFl" = twin_type "Dl");

val ctxt = Locale.init (loc thy "LFl") thy;
val _ = \<^assert> (Variable.is_fixed ctxt Syntax_Trans.implicit_structure_);
val _ = \<^assert> (not (Variable.is_fixed (Locale.init (loc thy "Dl") thy) Syntax_Trans.implicit_structure_));
(*a statement read in the block has no placeholder left: the replacement step ran*)
val _ = \<^assert> (not (has_placeholder (Syntax.read_prop ctxt "x \<otimes> y = x \<otimes> y")));
val _ = \<^assert> (not (exists (exists has_placeholder o #2) (assumes_of thy (loc thy "Hl1"))));
(*print_context's fixed variables line does not show it: stock's internal-name filter*)
val _ = \<^assert> (not (exists (String.isSubstring Syntax_Trans.implicit_structure_ o Pretty.string_of)
  (Proof_Context.pretty_ctxt (Config.put Proof_Context.debug true ctxt))));
(*the elimination environments of the twins are the inline expansions the plan names*)
fun eliminated_value twin x =
  after_elimination thy twin [x] (Free (x, the (AList.lookup (op =) (map #1 (Locale.params_of thy (loc thy twin))) x)));
val _ = \<^assert> (eliminated_value "Dl" "M" aconv reads (Locale.init (loc thy "Dl") thy) "S\<lparr>mult := \<lambda>x y. x\<rparr>");
val _ = \<^assert> (eliminated_value "D" "P" aconv reads (Locale.init (loc thy "D") thy) "UP S");
\<close>

(* a lemma in the block reads its statement through prep_full_context_statement with no
   imports: the header route has no cut and must leave the second layer Locale.init installed
   alone (plan 2192-2193); the stage-1000 step replaces the placeholder, so the goal, inspected
   while it is still open, has no placeholder (plan 5248-5249); the theory copy shows the cut in
   place (LFl has no assumptions, so the copy has no premise) *)
lemma (in LFl) lfl_stmt: "x \<otimes> y = x \<otimes> y"
  apply (tactic \<open>fn st => (\<^assert> (not (Test_Support.has_placeholder (Thm.prop_of st))); all_tac st)\<close>)
  apply (rule refl)
  done
ML \<open>
val expected =
  Proof_Context.read_term_pattern \<^context>
    "?x \<otimes>\<^bsub>?S\<lparr>mult := \<lambda>x y. x\<rparr>\<^esub> ?y = ?x \<otimes>\<^bsub>?S\<lparr>mult := \<lambda>x y. x\<rparr>\<^esub> ?y";
val _ =
  if Term.aconv_untyped (Thm.prop_of @{thm LFl.lfl_stmt}, HOLogic.mk_Trueprop expected) then ()
  else error ("LFl.lfl_stmt is\n" ^ @{make_string} (Thm.prop_of @{thm LFl.lfl_stmt}) ^ "\nexpected\n" ^ @{make_string} expected);
\<close>


subsection \<open>The instances are read before the body (plan 5232-5234)\<close>

locale H'' = LF + Gm + Cm "\<one>" + assumes h'': "x \<otimes> y = y \<otimes> x"

ML \<open>
val thy = \<^theory>;
val ctxt = Locale.init (loc thy "H''") thy;
(*the instance of C is G's one; the body's bare operator is UP S's*)
val _ = \<^assert> (eq_list (op aconv) (instances thy "Cm" "H''", [reads ctxt "\<one>\<^bsub>G\<^esub>"]));
val _ = \<^assert> (first_assumption thy "H''" aconv
  Syntax.read_prop ctxt "\<And>x y. x \<otimes>\<^bsub>UP S\<^esub> y = y \<otimes>\<^bsub>UP S\<^esub> x");
(*without a first layer the instance's bare index has nothing to denote; the twin's P does*)
val _ = fails_prefix "Illegal reference to implicit structure" (heavy thy "H''' = LF + Cm \"\<one>\"");
val _ = \<^assert> (can (heavy thy "DH''' = D + Cm \"\<one>\"") ());
\<close>

end
