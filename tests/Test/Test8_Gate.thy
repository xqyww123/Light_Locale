(* Plan section 7 test 8 (declaration shapes), the rows on the gate fixture UP_cring (parameters R, P
   with P == UP R): re-declaring the eliminated name in the for clause or in a body fixes (success,
   P a fresh parameter, exactly one D20 use warning, the declaration warning without its "not bound"
   sentence); the where mirrors; the stock for-clause duplicate check; the sibling-parameter rows
   (UP_cring "f P", UP_cring S "UP S"/"UP R" for S, annotated S); the structure variant LF'' with Pm;
   the recorded instance of P; independent type variables; the D20 use warning's two polarities in
   context LF; the header guard rows on the test-internal Pdef. *)
theory Test8_Gate
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>
open Test_Support;

val use_warning = "The parameter `P` from locale `UP_cring` is not bound any more and treated as a fresh variable here.";
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
  ["The following definitions from `UP_cring` are unfolded.\n  P \<equiv> UP R", "The parameter `P` from locale `UP_cring` is not bound any more and treated as a fresh variable here."]);
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
val _ = fails_with (not_bound "P" "UP (f P)" "UP_cring") (light thy "LX = UP_cring \"f P\"");
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

(* the header guard on the test-internal Pdef *)
consts pint :: "nat \<Rightarrow> nat set"  Q :: "nat set \<Rightarrow> bool"
locale Pdef = fixes Zp :: "nat set" and p :: nat defines "Zp \<equiv> pint p" assumes fin: "finite Zp"
locale M2 = fixes m :: "nat set" assumes "m = m"
light_locale LFP' = Pdef
ML \<open>
val thy = \<^theory>;
val guard = not_bound "Zp" "pint p" "Pdef";
(*the warnings a declaration emits before it fails with the guard error*)
fun guard_warnings f = #2 (with_warnings (fn () => fails_with guard f));
(*the rows whose eliminated name comes from their own header (plan line 5013): no warning*)
val _ = \<^assert> (null (guard_warnings (light thy "LX = Pdef + assumes ax: \"Q Zp\"")));
val _ = \<^assert> (null (guard_warnings (light thy "LX = Pdef + M2 Zp")));
(*the rows whose eliminated name comes from a light ancestor (LFP'): the D20 use warning, verbatim,
  at least once before the header error; the count is recorded in plan section 11 (30), not asserted*)
val use_warning_zp = "The parameter `Zp` from locale `Pdef` is not bound any more and treated as a fresh variable here.";
val _ = \<^assert> (member (op =) (guard_warnings (light thy "LX = LFP' + assumes ax: \"Q Zp\"")) use_warning_zp);
val _ = \<^assert> (member (op =) (guard_warnings (heavy thy "HX = LFP' + assumes ax: \"Q Zp\"")) use_warning_zp);
val _ = \<^assert> (member (op =) (guard_warnings (heavy thy "HX = LFP' + M2 Zp")) use_warning_zp);
(*positive and negative controls*)
val _ = \<^assert> (can (light thy "LY1 = Pdef + assumes ax: \"Q (pint p)\"") ());
val _ = \<^assert> (can (light thy "LY2 = Pdef + assumes ax: \"\<And>Zp. Q Zp\"") ());
\<close>
(*the two-hop variant (plan line 5010): the printed value is the one transformed by the morphism*)
light_locale LFPq = LFP' q for q
ML \<open>
val _ = fails_with (not_bound "Zp" "pint q" "Pdef") (heavy \<^theory> "HX2 = LFPq + assumes ax: \"Q Zp\"");
\<close>
context LFP' begin
ML_val \<open>
val _ = \<^assert> (member (op =) (guard_warnings (fn () =>
  Target_Context.context_begin_nested_cmd [] [Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]] (Context.Proof \<^context>))) use_warning_zp);
val _ = \<^assert> (can (Target_Context.context_begin_nested_cmd [] [Element.Fixes [(Binding.name "Zp", NONE, NoSyn)], Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]]) (Context.Proof \<^context>));
\<close>
end

end
