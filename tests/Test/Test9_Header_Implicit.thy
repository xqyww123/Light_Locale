(* Plan section 7 test 9 (structure), the header elements implicit_structure t and
   no_implicit_structure (header implicit structure plan, section 5, rows 1-22): a declared
   structure, the bare index positions of t, the joint type inference, at most one element, the
   cancellation and that no descendant inherits it, the ban on a light locale's own (structure)
   parameters, the free variable guards, the header attribute arguments, the query
   Locale.parent_implicit_structures, the heavy parser, a cut after a cancelled import, a goal
   expression under a declared structure, the declared structure of an import, and an eliminated
   position's own value beside such a cut.  Row 10 is the ban of 2026-10-23: no block of a locale
   sets the implicit structure.  R0 and R1 are the plan's fixtures, written out in full at every
   use.  Each positive row's comment says what it would show if the element were ignored.  The
   error texts marked measured were taken verbatim from the first run with the code (2026-10-22;
   E2 2026-10-23). *)
theory Test9_Header_Implicit
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;

val illegal_reference = "Illegal reference to implicit structure";
val at_most_one = "A light locale header declares at most one implicit structure";
val inside_locale =
  "You cannot set the implicit structure inside a locale. Declare it in the header of a light locale with implicit_structure instead.";

(*a Free with an internal name: the placeholder, or decl_, which t's own bare index positions take
  under a cut*)
val has_internal_free = Term.exists_subterm (fn Free (x, _) => Name.is_internal x | _ => false);

(*the parameters with schematic type variables: same_shape compares them up to a renaming of the
  type variables*)
fun params_term thy name =
  Logic.varify_types_global
    (list_comb (Free ("params", dummyT), map (Free o #1) (Locale.params_of thy (loc thy name))));

(*Locale.parent_implicit_structures of the locale, against (parent, term text read in the
  locale's block)*)
fun parents_are thy name expected =
  let
    val ctxt = Locale.init (loc thy name) thy;
    val want = map (fn (p, t) => (loc thy p, Option.map (reads ctxt) t)) expected;
  in
    \<^assert> (eq_list (fn ((p, t), (p', t')) => p = p' andalso eq_option (op aconv) (t, t'))
      (Locale.parent_implicit_structures thy (loc thy name), want))
  end;
\<close>


subsection \<open>Row 1: a declaration beside a written position\<close>

(* ignoring the element: the header fails with Illegal reference to implicit structure (where
   G = ... is a written position, not a cut) *)
light_locale NA = M: monoid where G = "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>" +
  implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>"
  assumes comm: "x \<otimes> y = y \<otimes> x"

ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "NA" aconv
  Syntax.read_prop \<^context>
    "\<And>x y. x \<otimes>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub> y = y \<otimes>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub> x")
\<close>
context NA
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>"))\<close>
(*the slot's type: the joint type inference with the body ties the carrier's type*)
ML \<open>val _ = \<^assert> (Option.map fastype_of (Syntax_Trans.implicit_structure \<^context>) = SOME \<^typ>\<open>nat monoid\<close>)\<close>
end


subsection \<open>Rows 2 and 3: the slot beats the cut, wherever the element stands\<close>

(* ignoring the element: the first assumption is on LF's cut UP S *)
light_locale X1 = LF + implicit_structure S assumes x1: "\<one> = \<one>"
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "X1" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "X1") \<^theory>) "\<one>\<^bsub>S\<^esub> = \<one>\<^bsub>S\<^esub>")
\<close>

(* ignoring the element: the block's second layer is UP S *)
light_locale X2 = LF + implicit_structure S
context X2
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end

(* ignoring the element: both first assumptions are on UP S.  P1's parameter f is also a constant
   of Test9_Fixtures: t read before the elements would see the constant and fail to type, so the
   row pins that t is read after all elements *)
light_locale P1 = LF + implicit_structure f fixes f :: "('c, 'd) ring_scheme" assumes p: "\<one> = \<one>"
light_locale P2 = LF + fixes R :: "('c, 'd) ring_scheme" assumes p: "\<one> = \<one>" implicit_structure R
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "P1" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "P1") \<^theory>) "\<one>\<^bsub>f\<^esub> = \<one>\<^bsub>f\<^esub>")
\<close>
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "P2" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "P2") \<^theory>) "\<one>\<^bsub>R\<^esub> = \<one>\<^bsub>R\<^esub>")
\<close>


subsection \<open>Row 4: at most one element\<close>

ML \<open>val _ = fails_with at_most_one (light \<^theory> "X3 = LF + implicit_structure S implicit_structure S")\<close>
ML \<open>val _ = fails_with at_most_one (light \<^theory> "X4 = LF + implicit_structure S no_implicit_structure")\<close>


subsection \<open>Row 5: t is typed together with the header's fixes and assumes\<close>

(* ignoring the element: the body reads UP S, so the untyped R stays a bare type variable and the
   parameters differ from the twin's *)
light_locale J1 = LF + fixes R implicit_structure R assumes j: "x \<otimes> y = y \<otimes> x"
locale J1h = LF + fixes R :: "('c, 'd) monoid_scheme" assumes j: "x \<otimes>\<^bsub>R\<^esub> y = y \<otimes>\<^bsub>R\<^esub> x"
ML \<open>val _ = \<^assert> (same_shape (params_term \<^theory> "J1", params_term \<^theory> "J1h"))\<close>

(* measured 2026-10-22 (build_7), approved by the user 2026-10-23: the type variable message, an
   instance of the approved template (the same function prints the block instance approved
   2026-10-16, Test9_Guards) *)
ML \<open>
val _ = fails_with "Undeclared type variables 'b, 'c in the implicit structure `\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>`, where `UNIV :: 'b set` and `0 :: 'c::{plus,zero}` require concrete type annotations."
  (light \<^theory> "J2 = M: monoid where G = \"\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\" + implicit_structure \"\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\"")
\<close>

(* measured: a type error of the body under the element shows the bare position and no internal
   name (the body keeps the placeholder, which the printer drops; a first version gave the body a
   second internal name and printed it) *)
ML \<open>
val _ = fails_prefix
  "Type unification failed: Clash of types \"nat\" and \"bool\"\n\nType error in application: incompatible operand type\n\nOperator:  (=) \<one> :: bool \<Rightarrow> bool\nOperand:   0 :: nat"
  (light \<^theory> "E1 = LF + implicit_structure S assumes e: \"\<one> = True \<and> \<one> = (0::nat)\"")
\<close>

(* measured (cslh19, 2026-10-23): a type error at one of t's own bare index positions under a cut
   prints that position with the internal name standing for the cut in t -- the known residual of
   the two-name reading (header plan section 3.3), pinned here *)
ML \<open>
val _ = fails_prefix
  "Type unification failed: Clash of types \"_ \<Rightarrow> _\" and \"bool\"\n\nType error in application: incompatible operand type\n\nOperator:  (\<and>) :: bool \<Rightarrow> bool \<Rightarrow> bool\nOperand:   \<one>\<^bsub>declared_structure_\<^esub> :: nat \<Rightarrow> 'a"
  (light \<^theory> "E2 = LF + implicit_structure \"(UP S)\<lparr>one := \<one> \<and> True\<rparr>\"")
\<close>


subsection \<open>Row 6: the slot is inherited by light and heavy descendants\<close>

(* ignoring NA's element: neither block has a second layer *)
light_locale NB = NA
locale HB = NA
context NB
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>"))\<close>
end
context HB
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>"))\<close>
end


subsection \<open>Row 7: the bare index positions of t\<close>

(* (i) t's bare \<one> reads the cut UP S.  Ignoring the element: the block's second layer is UP S and
   the first assumption is on UP S *)
light_locale K1 = LF + implicit_structure "(UP S)\<lparr>one := \<one>\<rparr>" assumes k: "\<one> = \<one>"
context K1
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "(UP S)\<lparr>one := \<one>\<^bsub>UP S\<^esub>\<rparr>"))\<close>
ML \<open>
val _ = \<^assert> (case Syntax_Trans.implicit_structure \<^context> of
  SOME t => not (has_internal_free t)
| NONE => false)
\<close>
end
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "K1" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "K1") \<^theory>)
    "\<one>\<^bsub>(UP S)\<lparr>one := \<one>\<^bsub>UP S\<^esub>\<rparr>\<^esub> = \<one>\<^bsub>(UP S)\<lparr>one := \<one>\<^bsub>UP S\<^esub>\<rparr>\<^esub>")
\<close>
ML \<open>val _ = \<^assert> (not (has_internal_free (first_assumption \<^theory> "K1")))\<close>

(* (ii) t's bare \<one> reads the inherited first layer G.  Ignoring the element: the block has no
   second layer *)
light_locale K2 = monoid + implicit_structure "G\<lparr>one := \<one>\<rparr>"
context K2
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "G\<lparr>one := \<one>\<^bsub>G\<^esub>\<rparr>"))\<close>
end

(* (iii) no import, no (structure) parameter: t's bare \<one> has nothing to denote *)
ML \<open>
val _ = fails_prefix illegal_reference
  (light \<^theory> "K3 = fixes G :: \"('a, 'b) monoid_scheme\" implicit_structure \"G\<lparr>one := \<one>\<rparr>\"")
\<close>


subsection \<open>Row 8: the cancellation\<close>

(* ignoring the element: a bare \<otimes> reads monoid's first layer G, and G's subscript is elided *)
light_locale NC = monoid + no_implicit_structure assumes nc: "x \<otimes>\<^bsub>G\<^esub> y = y \<otimes>\<^bsub>G\<^esub> x"
context NC
begin
ML \<open>val _ = fails_prefix illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
ML \<open>val _ = \<^assert> (can (reads \<^context>) "x \<otimes>\<^bsub>G\<^esub> y")\<close>
ML \<open>val _ = prints_as \<^context> "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes>\<^bsub>G\<^esub> y"\<close>
ML \<open>val _ = \<^assert> (round_trips \<^context> (reads \<^context> "x \<otimes>\<^bsub>G\<^esub> y"))\<close>
end
ML \<open>
val _ = fails_prefix illegal_reference
  (light \<^theory> "NC2 = monoid + no_implicit_structure assumes \"x \<otimes> y = y \<otimes> x\"")
\<close>


subsection \<open>Row 9: no descendant inherits a structure through the cancellation\<close>

(* ignoring NC's element: ND's bare \<otimes> reads G, and G's subscript is elided *)
light_locale ND = NC
context ND
begin
(* measured: the bare message of struct_tr, not wrapped *)
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
ML \<open>val _ = prints_as \<^context> "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes>\<^bsub>G\<^esub> y"\<close>
end
(* measured: the bare message of struct_tr, not wrapped *)
ML \<open>val _ = fails_with illegal_reference (light \<^theory> "ND2 = NC + assumes \"x \<otimes> y = y \<otimes> x\"")\<close>
(* measured: the bare message of struct_tr, not wrapped *)
ML \<open>val _ = fails_with illegal_reference (heavy \<^theory> "HD = NC + assumes \"x \<otimes> y = y \<otimes> x\"")\<close>

(* a descendant declares again.  Ignoring the element: NE has NC's cancellation and a bare \<otimes> is
   an error *)
light_locale NE = NC + implicit_structure G
context NE
begin
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "G")\<close>
end
(* measured: the bare message of struct_tr, not wrapped *)
ML \<open>
val _ = fails_with illegal_reference (light \<^theory> "NE2 = NC + implicit_structure \"G\<lparr>one := \<one>\<rparr>\"")
\<close>

(* after the cancellation the first remaining structure name is ring's R.  Ignoring NC's element:
   the first layer is NC's G, so the body and a bare \<otimes> read G, and G's subscript is elided *)
light_locale Q = NC + ring + assumes q: "x \<otimes> y = y \<otimes> x"
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "Q" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "Q") \<^theory>) "\<And>x y. x \<otimes>\<^bsub>R\<^esub> y = y \<otimes>\<^bsub>R\<^esub> x")
\<close>
context Q
begin
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "R")\<close>
ML \<open>val _ = prints_as \<^context> "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes>\<^bsub>G\<^esub> y"\<close>
end

(* a light locale cancels the (structure) parameter H it inherits from its heavy parent HCb:
   reopening it reads neither layer, its light and heavy descendants read nothing, and the query
   reports nothing *)
locale HCb = fixes H :: "('a, 'b) monoid_scheme" (structure)
light_locale HC = HCb + no_implicit_structure
context HC
begin
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
ML \<open>val _ = prints_as \<^context> "x \<otimes>\<^bsub>H\<^esub> y" "x \<otimes>\<^bsub>H\<^esub> y"\<close>
end
light_locale HC2 = HC
locale HC3 = HC
context HC2
begin
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
end
context HC3
begin
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
end
ML \<open>val _ = parents_are \<^theory> "HC2" [("HC", NONE)]\<close>

(* a heavy descendant's own (structure) parameter.  Ignoring NC's element: the first layer is NC's
   G, declared first, so the body and a bare \<otimes> read G *)
locale HE = NC + fixes H :: "('a, 'b) monoid_scheme" (structure) assumes he: "x \<otimes> y = y \<otimes> x"
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "HE" aconv
  Syntax.read_prop (Locale.init (loc \<^theory> "HE") \<^theory>) "\<And>x y. x \<otimes>\<^bsub>H\<^esub> y = y \<otimes>\<^bsub>H\<^esub> x")
\<close>
context HE
begin
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "H")\<close>
end


subsection \<open>Row 10: no block of a locale sets the implicit structure; clearing in a block and in a proof\<close>

(* the ban (2026-10-23) in a light locale's block, in a block nested in it and through the ML
   entry, judged before the value is read: the blank value, the inherited G and an undeclared y
   all get the one text *)
light_locale LMc = monoid
context LMc
begin
(*the fixture the proof row below relies on: LMc's block reads G*)
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "G")\<close>
ML \<open>
val _ = List.app (fn text => fails_with inside_locale (fn () => Light_Locale.set_implicit_structure_cmd text \<^context>))
  ["", "G", "y"]
\<close>
context
begin
ML \<open>val _ = fails_with inside_locale (fn () => Light_Locale.set_implicit_structure_cmd "G" \<^context>)\<close>
end
end

(* clearing in an unnamed block with a first layer G.  Ignoring the clearing: a bare \<otimes> reads
   G, and G's subscript is elided.  A nested block's clearing stays inside it; the ML entry with
   blanks gives what the command gives *)
context
  fixes G :: "('a, 'b) monoid_scheme" (structure)
begin
set_implicit_structure ""
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
ML \<open>val _ = prints_as \<^context> "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes>\<^bsub>G\<^esub> y"\<close>
set_implicit_structure "G"
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "G")\<close>
context
begin
set_implicit_structure ""
ML \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
end
ML \<open>val _ = \<^assert> (bare_denotes \<^context> "G")\<close>
ML \<open>
val _ = fails_with illegal_reference
  (fn () => reads (Light_Locale.set_implicit_structure_cmd "  " \<^context>) "x \<otimes> y")
\<close>
ML \<open>
val _ = prints_as (Light_Locale.set_implicit_structure_cmd "  " \<^context>) "x \<otimes>\<^bsub>G\<^esub> y"
  "x \<otimes>\<^bsub>G\<^esub> y"
\<close>
end

(* in a proof; only under a first layer does the cancellation differ from having no structure at
   all.  Ignoring the clearing: a bare \<otimes> reads G *)
context LMc
begin
notepad
begin
  with_implicit_structure "  "
  ML_prf \<open>val _ = fails_with illegal_reference (fn () => reads \<^context> "x \<otimes> y")\<close>
end
end


subsection \<open>Row 11: a light locale declares no (structure) parameter\<close>

ML \<open>
val _ = fails_with "A light locale does not declare (structure) parameters: \"G\". Write implicit_structure G instead."
  (light \<^theory> "B1 = fixes G :: \"('a, 'b) monoid_scheme\" (structure)")
\<close>
ML \<open>
val _ = fails_with "A light locale does not declare (structure) parameters: \"R\". Write implicit_structure R instead."
  (light \<^theory> "B2 = UP_cring R for R (structure)")
\<close>
ML \<open>
val _ = fails_with "A light locale does not declare (structure) parameters: \"G\", \"H\". Write implicit_structure with one of them instead."
  (light \<^theory> "B3 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) and H :: \"('a, 'b) monoid_scheme\" (structure)")
\<close>
(*the ban comes before the body's Illegal reference to implicit structure*)
ML \<open>
val _ = fails_with "A light locale does not declare (structure) parameters: \"G\". Write implicit_structure G instead."
  (light \<^theory> "B4 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) no_implicit_structure assumes \"x \<otimes> y = y \<otimes> x\"")
\<close>

(* the control: an inherited (structure) parameter is not the locale's own -- were it banned too,
   this declaration would fail *)
light_locale B5 = monoid
ML \<open>val _ = \<^assert> (#1 (layers (Locale.init (loc \<^theory> "B5") \<^theory>)) = SOME "G")\<close>


subsection \<open>Row 12: the free variable guards\<close>

ML \<open>
val g1 = "G1 = UP_cring S for S + implicit_structure \"UP y\"";
val g1_message =
  "Illegal undeclared variable \"y\" in the implicit structure. Only the parameters being declared may occur here: \"S\".";
\<close>
ML \<open>val _ = fails_with g1_message (light \<^theory> g1)\<close>
ML \<open>
val _ = fails_with "Illegal undeclared variables \"y\", \"z\" in the implicit structure. Only the parameters being declared may occur here: \"S\"."
  (light \<^theory> "G2 = LF + implicit_structure \"(UP S)\<lparr>carrier := y \<union> z\<rparr>\"")
\<close>
ML \<open>
val _ = fails_with "Illegal undeclared variable \"y\" in the implicit structure. No parameters are being declared in the locale, so no variable may occur here."
  (light \<^theory> "G3 = implicit_structure \"y\"")
\<close>
(*the hook: the guard's error comes alone, without the D20 declaration warning before it -- G1
  unfolds UP_cring's P, so a guard placed after the declaration would print that warning first*)
ML \<open>val _ = \<^assert> (null (rejected g1_message (light \<^theory> g1)))\<close>
(* measured: schematic variables in t, the stock check as for a defines element (Sign.no_vars) *)
ML \<open>
val _ = fails_with "Illegal schematic variable(s) in term: ?'a"
  (light \<^theory> "G4 = LF + implicit_structure \"undefined :: ?'a\"")
\<close>
ML \<open>val _ = fails_with "Illegal schematic variable(s) in term: ?x" (light \<^theory> "G5 = implicit_structure \"?x\"")\<close>

(* the block command in a locale's block: the ban comes before any guard (NP has no parameters,
   so the guard would have refused y) *)
light_locale NP
context NP
begin
ML \<open>val _ = fails_with inside_locale (fn () => Light_Locale.set_implicit_structure_cmd "y" \<^context>)\<close>
end

(* the block command in an unnamed block, only the placeholder fixed; R0 is annotated: nothing
   else ties its carrier's type *)
context
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr> :: nat monoid"
ML \<open>
val _ = fails_with "Illegal undeclared variable \"y\" in the implicit structure. No variables are fixed in this context, so no variable may occur here."
  (fn () => Light_Locale.set_implicit_structure_cmd "y" \<^context>)
\<close>
end


subsection \<open>Row 13: the header attribute arguments\<close>

(* ignoring the element: the attribute reads \<one> on the cut UP S *)
light_locale HA = LF + implicit_structure S assumes ax [t9_premise "\<one>"]: "\<one> = \<one>"
context HA
begin
ML \<open>val _ = premises_are \<^context> @{thm HA.ax [OF HA_axioms]} 1 "\<one>\<^bsub>S\<^esub> = \<one>\<^bsub>S\<^esub>"\<close>
end
(* measured: the attribute path gives the bare message, not wrapped, so fails_with and not the
   isSubstring precedent of Test9_Header_Attribute (row 10) *)
ML \<open>
val _ = fails_with illegal_reference
  (light \<^theory> "HA2 = monoid + no_implicit_structure assumes ax [t9_premise \"\<one>\"]: \"\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<^esub>\"")
\<close>
(* measured: as HA2 *)
ML \<open>
val _ = fails_with illegal_reference
  (light \<^theory> "HA3 = NC + assumes ax [t9_premise \"\<one>\"]: \"\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<^esub>\"")
\<close>


subsection \<open>Row 14: the element beats the import's slot\<close>

(* ignoring the element: IS1's first assumption is on R0, as IS2's *)
light_locale IS1 = NA + implicit_structure "\<lparr>carrier = UNIV, mult = (*), one = (1::nat)\<rparr>"
  assumes i: "\<one> = \<one>"
light_locale IS2 = NA + assumes i: "\<one> = \<one>"
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "IS1" aconv
  Syntax.read_prop \<^context>
    "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (*), one = (1::nat)\<rparr>\<^esub> = \<one>\<^bsub>\<lparr>carrier = UNIV, mult = (*), one = (1::nat)\<rparr>\<^esub>")
\<close>
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "IS2" aconv
  Syntax.read_prop \<^context>
    "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub> = \<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub>")
\<close>


subsection \<open>Row 15: a declaration beside a written position, without a body\<close>

(* ignoring the element: the block has no second layer.  R1 is annotated: without a body nothing
   else ties its carrier's type *)
light_locale NA2 = M: monoid where G = "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>" +
  implicit_structure "\<lparr>carrier = UNIV, mult = (*), one = (1::nat)\<rparr> :: nat monoid"
context NA2
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (*), one = (1::nat)\<rparr>"))\<close>
end


subsection \<open>Row 16: the query Locale.parent_implicit_structures\<close>

(* one entry per header edge: monoid's first layer G under the edge's morphism *)
light_locale NM = M: monoid where G = r + N: monoid where G = s for r s
ML \<open>val _ = parents_are \<^theory> "NM" [("monoid", SOME "r"), ("monoid", SOME "s")]\<close>

(* the query does not look at the locale's own slot: NM2's cancellation leaves the entry *)
light_locale NM2 = M: monoid where G = r for r + no_implicit_structure
ML \<open>val _ = parents_are \<^theory> "NM2" [("monoid", SOME "r")]\<close>

(* the other readings: a cancelled parent gives nothing and ring's R stays; LF's cut comes under
   the edge's morphism; Q's first remaining structure name R is reported, not a first-layer head; NP has no
   structure at all.  A mapping that dropped the morphism would show UP S for PS; one that read
   the first layer would show G for Q's NC edge *)
ML \<open>val _ = parents_are \<^theory> "Q" [("NC", NONE), ("ring", SOME "R")]\<close>
light_locale PS = LF T for T
ML \<open>val _ = parents_are \<^theory> "PS" [("LF", SOME "UP T")]\<close>
light_locale QQ = Q
ML \<open>val _ = parents_are \<^theory> "QQ" [("Q", SOME "R")]\<close>
light_locale NPP = NP
ML \<open>val _ = parents_are \<^theory> "NPP" [("NP", NONE)]\<close>


subsection \<open>Row 17: the heavy parser does not know the elements\<close>

ML \<open>val _ = fails_prefix "Outer syntax error" (heavy \<^theory> "X5 = LF + fixes x implicit_structure t")\<close>


subsection \<open>Row 18: a cut after a cancelled import counts\<close>

(* NC cancels, NA declares R0 behind it: the cut is found, so the header and the block read R0.
   Were the cancellation looked at before the cut, in the summary or in the state, NF would read
   nothing *)
light_locale NF = NC + NA + assumes nf: "\<one> = \<one>"
ML \<open>
val _ = \<^assert> (first_assumption \<^theory> "NF" aconv
  Syntax.read_prop \<^context>
    "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub> = \<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>\<^esub>")
\<close>
context NF
begin
ML \<open>val _ = \<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = (0::nat)\<rparr>"))\<close>
end


subsection \<open>Row 19: a goal expression under a declared structure reads that structure\<close>

(* inside LF's block a bare index position reads UP S, whatever the imports of a goal expression
   give (Test9_XO states the invariant for a cut): over HC the imports give the cancelled state,
   over HQ = HC + Bt with T left uninstantiated the remaining name T -- both states pinned through
   Locale.imports_structure_state.  Were the imports' state installed instead (no value under the
   cancellation, the placeholder itself under the remaining name), the bare one of the instance
   would stay the internal placeholder in both cases *)
locale HQ = HC + Bt
ML \<open>local
val thy = \<^theory>;
val _ = \<^assert> (Locale.imports_structure_state thy [] [(loc thy "HC", [Locale.Written])] =
  Locale.Cancelled_Structure);
val _ = \<^assert> (Locale.imports_structure_state thy [] [(loc thy "HQ", [Locale.Written, Locale.Inherited])] =
  Locale.Structure_Head "T");
in end\<close>
(* one lemma per locale: a failing ML_prf ends its proof, so a mutant run shows each red on its own *)
context LF
begin
lemma "True"
proof -
  interpret I: HC "(UP S)\<lparr>one := \<one>\<rparr>" .
  ML_prf \<open>
    val thy = \<^theory>;
    val insts =
      Locale.instance_of thy (loc thy "HC")
        (#2 (the_single (Locale.registrations_of (Context.Proof \<^context>) (loc thy "HC"))));
    val _ = \<^assert> (not (exists has_internal_free insts));
    val _ = \<^assert> (Term.aconv_untyped (hd insts, reads \<^context> "(UP S)\<lparr>one := \<one>\<^bsub>UP S\<^esub>\<rparr>"));
  \<close>
  show True ..
qed
lemma "True"
proof -
  interpret J: HQ "(UP S)\<lparr>one := \<one>\<rparr>" .
  ML_prf \<open>
    val thy = \<^theory>;
    val insts =
      Locale.instance_of thy (loc thy "HQ")
        (#2 (the_single (Locale.registrations_of (Context.Proof \<^context>) (loc thy "HQ"))));
    val _ = \<^assert> (not (exists has_internal_free insts));
    val _ = \<^assert> (Term.aconv_untyped (hd insts, reads \<^context> "(UP S)\<lparr>one := \<one>\<^bsub>UP S\<^esub>\<rparr>"));
  \<close>
  show True ..
qed
end


subsection \<open>Row 20: the declared structure of an import\<close>

(* a fully written import's declared structure arrives like a cut (plan 5300-5301): KG opens with
   LGm's f at X and Bt's T as the first layer.  Ignoring LGm's element: no second layer *)
light_locale LGm = Gm + implicit_structure "f G"
locale KG = LGm X + Bt for X
ML \<open>local
val ctxt = Locale.init (loc \<^theory> "KG") \<^theory>;
val _ = \<^assert> (#1 (layers ctxt) = SOME "T");
val _ = \<^assert> (implicit_is ctxt (reads ctxt "f X"));
in end\<close>

(* a declared structure on the second import only (plan 5301): ring's surviving R arrives first,
   so CR opens with R as the first layer and no second layer.  Ignoring LCM's element changes
   nothing here; were the declared structure preferred to a surviving name before it, CR would
   read f R *)
light_locale LCM = comm_monoid + implicit_structure "f G"
locale CR = ring + LCM R
ML \<open>val _ = \<^assert> (layers (Locale.init (loc \<^theory> "CR") \<^theory>) = (SOME "R", NONE))\<close>


subsection \<open>Row 21: a declared term with a binder reaches a child\<close>

(* plan 5245-5247: the child declared afterwards reads the term, and its bare operator has the
   type of the heavy twin's operator after elimination.  Ignoring LFlb's element: the child reads
   LFl's cut S\<lparr>mult := \<lambda>x y. x\<rparr> *)
light_locale LFlb = UPl S for S + implicit_structure "S\<lparr>mult := \<lambda>x y. y\<rparr>"
locale Hlb = LFlb + fixes z :: 'a
locale DHl = Dl + fixes z :: 'a
ML \<open>local
val thy = \<^theory>;
val ctxt = Locale.init (loc thy "Hlb") thy;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "S\<lparr>mult := \<lambda>x y. y\<rparr>"));
val _ = \<^assert> (bare_denotes ctxt "S\<lparr>mult := \<lambda>x y. y\<rparr>");
val _ = \<^assert> (fastype_of (reads ctxt "x \<otimes> y") =
  fastype_of (after_elimination thy "DHl" ["M"] (reads (Locale.init (loc thy "DHl") thy) "x \<otimes> y")));
in end\<close>


subsection \<open>Row 22: an eliminated position's own value beats the import's inherited cut\<close>

(* UPx's summary carries both surviving names (UPm's R, P) and the cut LCM2 declares (f (f R)), the
   names first: UPx itself opens with R and no second layer, and the light LX, which eliminates P,
   reads P's own value f S -- as does its descendant HX (plan decision 16 (c), example (ii); the
   header form of the retired Test9_Slot_Monoid rows LF/H5m/UP_cring).  An implementation taking
   the import's inherited cut at the eliminated position would read f (f S) *)
light_locale LCM2 = comm_monoid + implicit_structure "f (f G)"
locale UPx = UPm + LCM2 R
light_locale LX = UPx S for S
locale HX = LX + comm_monoid G for G
ML \<open>local
val thy = \<^theory>;
fun opened name = Locale.init (loc thy name) thy;
val _ = \<^assert> (layers (opened "UPx") = (SOME "R", NONE));
val _ = \<^assert> (implicit_is (opened "LX") (reads (opened "LX") "f S"));
val _ = \<^assert> (implicit_is (opened "HX") (reads (opened "HX") "f S"));
in end\<close>

end
