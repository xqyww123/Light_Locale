(* Plan section 7 test 8 (declaration shapes), the rows on the gate fixture UP_cring (parameters R, P
   with P == UP R): re-declaring the eliminated name in the for clause or in a body fixes (success,
   P a fresh parameter, exactly one D20 use warning, the declaration warning without its "not bound"
   sentence); the where mirrors; the stock for-clause duplicate check; the sibling-parameter rows
   (UP_cring "f P", UP_cring S "UP S"/"UP R" for S, annotated S); the structure variant LF'' with Pm;
   the recorded instance of P; independent type variables; the D20 use warning's two polarities in
   context LF; the rows writing an eliminated name where it is not bound, on the test-internal
   Pdef (the use warning, then stock's closure or stock's free-variable error; at an
   incompatible type no use warning). *)
theory Test8_Gate
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>
open Test_Support;

val use_warning = eliminated_name_warning "P" "UP_cring";
val decl_warning = "The following definitions from `UP_cring` are unfolded.\n  P \<equiv> UP S";
\<close>

(* the eliminated name written again in the for clause: P is a fresh parameter, last *)
light_locale LFP = UP_cring S for S and P
ML \<open>
val thy = \<^theory>;
val ps = Locale.params_of thy (loc thy "LFP");
val _ = \<^assert> (map (#1 o #1) ps = ["S", "P"]);
(*P is not in the assumptions (own and inherited: the predicate statement, plan line 5018) and
  nothing is defined*)
val (asm, defs) = Locale.specification_of thy (loc thy "LFP");
val _ = \<^assert> (null defs);
val _ = \<^assert> (not (member (op =) (map #1 (Term.add_frees (the asm) [])) "P"));
val _ = \<^assert> (sort_strings (declares thy "LFP1 = UP_cring S for S and P") = [decl_warning, use_warning]);
val _ = \<^assert> (sort_strings (declares thy "LFP2 = UP_cring S \"UP S\" for S and P") = [decl_warning, use_warning]);
val _ = \<^assert> (sort_strings (declares thy "LFP3 = UP_cring where P = _ for P") =
  ["The following definitions from `UP_cring` are unfolded.\n  P \<equiv> UP R", use_warning]);
val _ = \<^assert> (sort_strings (declares thy "LFP4 = UP_cring where R = S and P = \"UP S\" for S and P") = [decl_warning, use_warning]);
val _ = fails_with (defined_as "2nd" "P" "UP_cring" "UP R") (light thy "LX = UP_cring where P = \"UP S\" for S and P");
(*the gate fixture itself: no use warning, the declaration warning with its last sentence*)
val lfe_warning = decl_warning ^ "\nThe names `P` are not bound and shouldn't be used any more. Write their unfolded terms instead.";
val _ = \<^assert> (declares thy "LFe = UP_cring S for S" = [lfe_warning]);
(*the third layout (plan line 5004): two UP_cring instances in one header, one unfolded term each,
  the last sentence naming P once -- the same text as for LFe*)
val _ = \<^assert> (declares thy "LF2i = A: UP_cring S + B: UP_cring T for S T" = [lfe_warning]);
\<close>

light_locale LFe = UP_cring S for S
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (null (declares thy "LFg' = LFe + fixes P"));
\<close>
light_locale LFg' = LFe + fixes P
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (member (op =) (map (#1 o #1) (Locale.params_of thy (loc thy "LFg'"))) "P");
val _ = fails_with "Parameter(s) declared simultaneously in expression and for clause: R" (light thy "LX = UP_cring for R");
\<close>
(*the eliminated name in this import's own instance (plan line 5013; user 2026-10-16 (a)): the
  D20 use warning, then stock's free-variable error*)
ML_val \<open>
val ws = rejected "Illegal free variables in expression: \"f\", \"P\"" (light thy "LX = UP_cring \"f P\"");
val _ = \<^assert> (member (op =) ws use_warning);
\<close>
ML \<open>
val _ = fails_with (defined_as "2nd" "P" "UP_cring" "UP S") (light thy "LX = UP_cring S \"UP R\" for S");
val _ = fails_with (defined_as "2nd" "P" "UP_cring" "UP S") (light thy "LX = UP_cring \"S :: ('c,'d) ring_scheme\" \"UP R\" for S");
\<close>

light_locale LFu = UP_cring S "UP S" for S
light_locale LFt = UP_cring "S :: ('c,'d) ring_scheme" "UP S" for S
light_locale LFt' = UP_cring "S :: ('c,'d) ring_scheme" _ for S
locale Pm = fixes P :: "('a, nat \<Rightarrow> 'a) up_ring"
light_locale LF'' = UP_cring S + Pm for S
light_locale LFb = UP_cring S for S + fixes P
light_locale LFs = UP_cring S for S :: "('c,'d) ring_scheme"
light_locale LF2i = A: UP_cring S + B: UP_cring T for S T

ML \<open>
val thy = \<^theory>;
fun same (a, b) =
  params thy (loc thy a) = params thy (loc thy b) andalso
  #2 (Locale.specification_of thy (loc thy a)) = #2 (Locale.specification_of thy (loc thy b)) andalso
  instances thy "UP_cring" (loc thy a) = instances thy "UP_cring" (loc thy b);
val _ = \<^assert> (same ("LFu", "LFe"));
val _ = \<^assert> (same ("LFt", "LFt'"));
(*Pm's P is an implicit parameter of the import: it precedes the for parameter S, as in the heavy twin D*)
val _ = \<^assert> (map (#1 o #1) (Locale.params_of thy (loc thy "LF''")) = ["P", "S"]);
val _ = \<^assert> (map (#1 o #1) (Locale.params_of thy (loc thy "LFb")) = ["S", "P"]);
val _ = \<^assert> (sort_strings (declares thy "LFb2 = UP_cring S for S + fixes P") = [decl_warning, use_warning]);
(*the recorded instance of P is the unfolded term UP S*)
val _ = \<^assert> (instances thy "UP_cring" (loc thy "Light_Locale_Base.LF") = [\<^term>\<open>S :: ('a, 'b) ring_scheme\<close>, \<^term>\<open>UP (S :: ('a, 'b) ring_scheme)\<close>]);
(*two instances in one header have independent type variables*)
val [(_, sT, _), (_, tT, _)] = params thy (loc thy "LF2i");
val _ = \<^assert> (null (inter (op =) (Term.add_tfreesT sT []) (Term.add_tfreesT tT [])));
\<close>

(* the D20 use warning in context LF: incompatible type, no warning; UnivPoly-shaped statement, one *)
context LF begin
local_setup \<open>fn lthy =>
  let
    val (lthy1, w1) = with_warnings (fn () => theorem_in lthy (Binding.name "u1") "[]" "P x \<Longrightarrow> P x" (fn c => assume_tac c));
    val _ = \<^assert> (null w1);
    val (lthy2, w2) = with_warnings (fn () => theorem_in lthy1 (Binding.name "u2") "[]" "coeff P f n = coeff P f n" (fn c => resolve_tac c @{thms refl}));
    val _ = \<^assert> (w2 = [use_warning]);
  in lthy2 end\<close>
end
(*the same statement through lemma (in LF) (plan line 5004)*)
ML \<open>
val _ = \<^assert> (#2 (with_warnings (fn () =>
  lemma_in "LF" (Binding.name "u3") "[]" "coeff P f n = coeff P f n" (fn c => resolve_tac c @{thms refl}) \<^theory>)) = [use_warning]);
\<close>

(* the eliminated name written where it is not bound (plan section 6, decision 1 (v)-(vi); user
   2026-10-16 (a)), on the test-internal Pdef (Zp == pint p): the D20 use warning, then stock's
   behaviour -- an element closes the name (\<And>Zp.) and the declaration succeeds with the
   parameters unchanged, an instance position fails with stock's free-variable error *)
consts pint :: "nat \<Rightarrow> nat set"  Q :: "nat set \<Rightarrow> bool"
locale Pdef = fixes Zp :: "nat set" and p :: nat defines "Zp \<equiv> pint p" assumes fin: "finite Zp"
locale M2 = fixes m :: "nat set" assumes "m = m"
light_locale LFP' = Pdef
(* the controls: the unfolded term written, and Zp closed explicitly *)
light_locale LY1 = Pdef + assumes ax: "Q (pint p)"
light_locale LY2 = Pdef + assumes ax: "\<And>Zp. Q Zp"
ML \<open>
val thy = \<^theory>;
val use_warning_zp = eliminated_name_warning "Zp" "Pdef";
val illegal_zp = "Illegal free variables in expression: \"Zp\"";
val pdef_warning = "The following definitions from `Pdef` are unfolded.\n  Zp \<equiv> pint p\nThe names `Zp` are not bound and shouldn't be used any more. Write their unfolded terms instead.";
(*what the declaration records is the control's: the assumption with Zp closed; the parameters*)
fun closes_zp (name, thy') = assumes_of thy' name = assumes_of thy' (loc thy' "LY2");
fun params_as control (name, thy') = params thy' name = params thy' (loc thy' control);
\<close>
(*the name eliminated by the header itself, in an element: one warning, the closure*)
ML_val \<open>
val (lx, ws) = accepted (light thy "LX = Pdef + assumes ax: \"Q Zp\"");
val _ = \<^assert> (ws = [use_warning_zp, pdef_warning] andalso closes_zp lx andalso params_as "LY2" lx);
\<close>
(*at an incompatible type: no use warning, as with lemma (REV8-1)*)
ML_val \<open>
val (_, ws) = accepted (light thy "LX = Pdef + assumes ax: \"Zp = (0::nat)\"");
val _ = \<^assert> (ws = [pdef_warning]);
\<close>
(*the same name at a later import's instance position, and at an earlier one's -- the check at
  the end of each import sees every instance so far; the warning can repeat, once per name per
  type check (section 11 (30)), and the count is not asserted*)
ML_val \<open>\<^assert> (member (op =) (rejected illegal_zp (light thy "LX = Pdef + M2 Zp")) use_warning_zp)\<close>
ML_val \<open>\<^assert> (member (op =) (rejected illegal_zp (light thy "LX = M2 Zp + Pdef")) use_warning_zp)\<close>
(*a light ancestor's name (LFP'), in light and heavy headers; the count of the warning is
  recorded in plan section 11 (30), not asserted*)
ML_val \<open>
val (lx, ws) = accepted (light thy "LX = LFP' + assumes ax: \"Q Zp\"");
val _ = \<^assert> (member (op =) ws use_warning_zp andalso closes_zp lx andalso params_as "LY2" lx);
\<close>
ML_val \<open>
val (hx, ws) = accepted (heavy thy "HX = LFP' + assumes ax: \"Q Zp\"");
val _ = \<^assert> (member (op =) ws use_warning_zp andalso closes_zp hx andalso params_as "LY2" hx);
\<close>
ML_val \<open>\<^assert> (member (op =) (rejected illegal_zp (heavy thy "HX = LFP' + M2 Zp")) use_warning_zp)\<close>
(*a kept written position beside an element naming P: one use warning (with the declaration
  warning), P closed -- the table holds the kept position's parse result under the parameter's
  type constraint, so the type comparison reads that type and never the parse result's dummy
  types, which would raise TERM*)
light_locale LY3 = UP_cring S "UP S" for S + assumes ax: "\<And>P. P = UP S"
ML_val \<open>
val (lx, ws) = accepted (light \<^theory> "LX = UP_cring S \"UP S\" for S + assumes ax: \"P = UP S\"");
val _ = \<^assert> (sort_strings ws = [lfe_warning, use_warning]);
val _ = \<^assert> (assumes_of (#2 lx) (#1 lx) = assumes_of (#2 lx) (loc (#2 lx) "LY3") andalso params_as "LY3" lx);
\<close>
(*the two-hop variant (plan line 5010): the table entry carried through the morphism names the
  defining locale*)
light_locale LFPq = LFP' q for q
ML_val \<open>
val (hx, ws) = accepted (heavy \<^theory> "HX2 = LFPq + assumes ax: \"Q Zp\"");
val _ = \<^assert> (member (op =) ws use_warning_zp andalso closes_zp hx);
\<close>
(*a nested context's assumes inside the light block: the warning, the closure (the assumed
  proposition, the fact's hyp; its statement is normalised to Q ?Zp); with Zp fixed there, nothing*)
context LFP' begin
ML_val \<open>
val ctxt = \<^context>;
val (lthy, ws) = with_warnings (fn () =>
  Target_Context.context_begin_nested_cmd [] [Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]] (Context.Proof ctxt));
val _ = \<^assert> (member (op =) ws use_warning_zp);
val _ = \<^assert> (the_single (Thm.hyps_of (Proof_Context.get_thm lthy "hy")) aconv Syntax.read_prop ctxt "\<And>Zp. Q Zp" andalso
  not (Variable.is_fixed lthy "Zp"));
val _ = \<^assert> (null (#2 (with_warnings (fn () =>
  Target_Context.context_begin_nested_cmd [] [Element.Fixes [(Binding.name "Zp", NONE, NoSyn)], Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]] (Context.Proof ctxt)))));
\<close>
end

end
