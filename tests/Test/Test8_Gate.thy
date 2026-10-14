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
val strip = XML.content_of o YXML.parse_body;
(*the declaration must fail with exactly this message*)
fun fails_with expected f =
  ((f (); error "accepted") handle ERROR msg =>
    if strip msg = expected then () else error ("got:\n" ^ strip msg ^ "\nexpected:\n" ^ expected));
fun fails_prefix expected f =
  ((f (); error "accepted") handle ERROR msg =>
    if String.isPrefix expected (strip msg) then () else error ("got:\n" ^ strip msg));
fun defined_as ord y loc shown =
  "The " ^ ord ^ " parameter `" ^ y ^ "` of locale `" ^ loc ^ "` is defined as `" ^ shown ^
    "` and cannot be instantiated. You must write `_`.";
fun not_bound x t loc =
  "A light locale does not support definitions. `" ^ x ^ " \<equiv> " ^ t ^ "` from locale `" ^ loc ^
    "` is unfolded and `" ^ x ^ "` is not bound here. Write `" ^ t ^ "` instead.";
fun light thy text = fn () => light_locale_cmd text thy;
fun heavy thy text = fn () => locale_cmd text thy;
fun params thy l = map (fn ((x, T), mx) => (x, T, Mixfix.equal (mx, NoSyn))) (Locale.params_of thy l);
fun loc thy n = Locale.check_global thy (n, Position.none);
(*the morphism of the edge from parent p to l, and the instances of p's parameters under it*)
fun edge thy p l =
  the (find_first (fn {source, target, ...} => source = loc thy p andalso target = loc thy l)
    (Locale.dest_dependencies [] thy)) |> #morphism;
fun instances thy p l = Locale.instance_of thy (loc thy p) (edge thy p l);
fun tfrees ts = fold Term.add_tfrees ts [];

val use_warning = "The parameter `P` from locale `UP_cring` is not bound any more and treated as a fresh variable here.";
val decl_warning = "The following definitions from `UP_cring` are unfolded.\n  P \<equiv> UP S";
fun declares thy text = #2 (with_warnings (fn () => light_locale_cmd text thy));
\<close>

(* the eliminated name written again in the for clause: P is a fresh parameter, last *)
light_locale LFP = UP_cring S for S and P
ML \<open>
val thy = \<^theory>;
val ps = Locale.params_of thy (loc thy "LFP");
val _ = \<^assert> (map (#1 o #1) ps = ["S", "P"]);
val _ = \<^assert> (null (#2 (Locale.specification_of thy (loc thy "LFP"))));
val _ = \<^assert> (not (exists (fn Element.Assumes asms => exists (fn (_, ps) => exists (fn (t, _) => Term.exists_subterm (fn Free ("P", _) => true | _ => false) t) ps) asms | _ => false)
  (Locale.hyp_spec_of thy (loc thy "LFP"))));
val _ = \<^assert> (sort_strings (declares thy "LFP1 = UP_cring S for S and P") = [decl_warning, use_warning]);
val _ = \<^assert> (sort_strings (declares thy "LFP2 = UP_cring S \"UP S\" for S and P") = [decl_warning, use_warning]);
val _ = \<^assert> (sort_strings (declares thy "LFP3 = UP_cring where P = _ for P") =
  ["The following definitions from `UP_cring` are unfolded.\n  P \<equiv> UP R", "The parameter `P` from locale `UP_cring` is not bound any more and treated as a fresh variable here."]);
val _ = \<^assert> (sort_strings (declares thy "LFP4 = UP_cring where R = S and P = \"UP S\" for S and P") = [decl_warning, use_warning]);
val _ = fails_with (defined_as "2nd" "P" "UP_cring" "UP R") (light thy "LX = UP_cring where P = \"UP S\" for S and P");
(*the gate fixture itself: no use warning, the declaration warning with its last sentence*)
val _ = \<^assert> (declares thy "LFe = UP_cring S for S" =
  [decl_warning ^ "\nThe names `P` are not bound and shouldn't be used any more. Write their unfolded terms instead."]);
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

(* the header guard on the test-internal Pdef *)
consts pint :: "nat \<Rightarrow> nat set"  Q :: "nat set \<Rightarrow> bool"
locale Pdef = fixes Zp :: "nat set" and p :: nat defines "Zp \<equiv> pint p" assumes fin: "finite Zp"
locale M2 = fixes m :: "nat set" assumes "m = m"
light_locale LFP' = Pdef
ML \<open>
val thy = \<^theory>;
val guard = not_bound "Zp" "pint p" "Pdef";
val _ = fails_with guard (light thy "LX = Pdef + assumes ax: \"Q Zp\"");
val _ = fails_with guard (light thy "LX = LFP' + assumes ax: \"Q Zp\"");
val _ = fails_with guard (heavy thy "HX = LFP' + assumes ax: \"Q Zp\"");
val _ = fails_with guard (light thy "LX = Pdef + M2 Zp");
val _ = fails_with guard (heavy thy "HX = LFP' + M2 Zp");
(*the own-header rows emit no warning before the error*)
val _ = \<^assert> (null (#2 (with_warnings (fn () => (light thy "LX = Pdef + assumes ax: \"Q Zp\"" (); ()) handle ERROR _ => ()))));
(*positive and negative controls*)
val _ = \<^assert> (can (light thy "LY1 = Pdef + assumes ax: \"Q (pint p)\"") ());
val _ = \<^assert> (can (light thy "LY2 = Pdef + assumes ax: \"\<And>Zp. Q Zp\"") ());
\<close>
context LFP' begin
ML_val \<open>
val _ = fails_with (not_bound "Zp" "pint p" "Pdef") (fn () =>
  Target_Context.context_begin_nested_cmd [] [Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]] (Context.Proof \<^context>));
val _ = \<^assert> (can (Target_Context.context_begin_nested_cmd [] [Element.Fixes [(Binding.name "Zp", NONE, NoSyn)], Element.Assumes [((Binding.name "hy", []), [("Q Zp", [])])]]) (Context.Proof \<^context>));
\<close>
end

end
