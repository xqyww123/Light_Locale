(* Plan section 7 test 8 (declaration shapes): the beta-normal-form rows LB/LB', the batch-mode
   annotation row LZ on Hz, the joint per-position check fixture Two (LT1/LT3), the specialised
   annotation LP against the twin LPh over the defines-free parent Parent0 (LPh0 fails with "Bad
   arguments on lhs"), the Fin/LFn rows, the LK/LK2/LK3/LK3h/LK3d/LKe rows read through
   Locale.dest_dependencies and Locale.instance_of, the conflict row LC (stock's type error), the
   four defines/notes rows with the section-6 texts verbatim, and the D20 declaration warning in
   its single-source and two-source layouts. *)
theory Test8_Eliminated
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale Parent = fixes g :: "'a \<Rightarrow> 'b" and x :: 'a and y :: 'b defines "y \<equiv> g x"
locale Parent0 = fixes g :: "'a \<Rightarrow> 'b" and x :: 'a and y :: 'b

(* beta normal form *)
light_locale LB = Parent "\<lambda>n::nat. n + 1" 3 "3 + 1"
ML \<open>
val _ = fails_with (defined_as "3rd" "y" "Parent" "3 + 1") (light \<^theory> "LB' = Parent \"\<lambda>n::nat. n + 1\" 3 \"3 + 2\"");
\<close>

(* the annotation printed in batch mode (plan lines 5088-5092): the fourth slot carries `::` and no
   schematic type variable in the defined-position message (LZ) *)
locale Hz = fixes g :: "'a::numeral \<Rightarrow> 'a" and d :: 'a defines "d \<equiv> g 2"
light_locale LHz = Hz h "h 2" for h
ML \<open>
(*the prefix, and no ? anywhere in the message: a check neither fails_with nor fails_prefix expresses*)
fun annotated prefix =
  fails_checked ("prefix without ?:\n" ^ prefix)
    (fn s => String.isPrefix prefix s andalso not (exists_string (fn c => c = "?") s));
val _ = annotated "The 2nd parameter `d` of locale `Hz` is defined as `h (2::" (light \<^theory> "LZ = Hz h \"h 3\" for h");
\<close>

(* the joint per-position check *)
locale Two = fixes g :: "nat \<Rightarrow> nat" and x y z :: nat defines "y \<equiv> g x" and "z \<equiv> g (g x)"
consts g0 :: "nat \<Rightarrow> nat"
ML \<open>
val _ = fails_with (defined_as "3rd" "y" "Two" "f v") (light \<^theory> "LT1 = Two f v \"f (f v)\" \"True\" for f v");
val _ = fails_with (defined_as "4th" "z" "Two" "f (f v)") (light \<^theory> "LT3 = Two f v \"f v\" \"g0 (g0 v)\" for f v");
\<close>

(* the specialised annotation takes effect, as in the twin over the defines-free parent *)
light_locale LP = Parent f v "(f v :: nat)" for f v
locale LPh = Parent0 f v "(f v :: nat)" for f v
light_locale LP0 = Parent f v _ for f v
ML \<open>
val thy = \<^theory>;
val _ = assert_twin thy (loc thy "LP", loc thy "LPh");
val [("f", Type ("fun", [dom, ran]), _), ("v", vT, _)] = params thy (loc thy "LP");
val _ = \<^assert> (ran = \<^typ>\<open>nat\<close> andalso dom = vT);
val [("f", Type ("fun", [_, ran0]), _), _] = params thy (loc thy "LP0");
val _ = \<^assert> (is_TFree ran0);
val _ = fails_prefix "Bad arguments on lhs" (heavy \<^theory> "LPh0 = Parent f v \"(f v :: nat)\" for f v");
(*the type variables fixed in for and then nat at the defined position (plan line 4991): stock's
  type error, not a section-6 message*)
val _ = fails_prefix "Type unification failed" (light \<^theory> "LX = Parent f v \"(f v :: nat)\" for f :: \"'a \<Rightarrow> 'b\" and v");
\<close>

(* a copied-back term of another type fills the unfolded term *)
locale Fin = fixes b :: bool defines "b \<equiv> finite (UNIV :: 'a set)"
light_locale LFn = Fin "finite UNIV"
light_locale LFn2 = Fin _
light_locale LFn3 = Fin "finite (UNIV :: nat set)"
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (instances thy "Fin" (loc thy "LFn") = instances thy "Fin" (loc thy "LFn2"));
val _ = \<^assert> (length (tfrees (instances thy "Fin" (loc thy "LFn"))) = 1);
(*a copied-back term of another type: the unfolded term is recorded, as for _*)
val _ = \<^assert> (instances thy "Fin" (loc thy "LFn3") = instances thy "Fin" (loc thy "LFn2"));
\<close>

(* the unfolded term and the outer type: LK, LK2, LKe *)
light_locale LK = Parent card UNIV _
locale Parent2 = fixes g :: "'a \<Rightarrow> 'b" and x :: 'a and w :: 'a and y :: 'b defines "y \<equiv> g x"
light_locale LK2 = Parent2 card UNIV w _ for w
light_locale LKe = Parent2 "\<lambda>S (n::nat). card S + n" UNIV w "plus (card (UNIV :: 'z set))" for w :: "'z set"
ML \<open>
val thy = \<^theory>;
val m = edge thy "Parent" (loc thy "LK");
val [g, x, y] = instances thy "Parent" (loc thy "LK");
val [(gn, gT), (xn, xT), _] = map #1 (Locale.params_of thy (loc thy "Parent"));
val _ = \<^assert> (y aconv Morphism.term m (Free (gn, gT) $ Free (xn, xT)));
val _ = \<^assert> (length (tfrees [g, x, y]) = 1);
val [_, _, w2, y2] = instances thy "Parent2" (loc thy "LK2");
val [(_, wT, _)] = params thy (loc thy "LK2");
val _ = \<^assert> (y2 aconv (Const (\<^const_name>\<open>card\<close>, HOLogic.mk_setT (HOLogic.dest_setT wT) --> \<^typ>\<open>nat\<close>) $ HOLogic.mk_UNIV (HOLogic.dest_setT wT)));
val ye = List.last (instances thy "Parent2" (loc thy "LKe"));
val _ = \<^assert> (ye aconv \<^term>\<open>plus (card (UNIV :: 'z set))\<close>);
val _ = \<^assert> (not (ye aconv \<^term>\<open>\<lambda>n. card (UNIV :: 'z set) + n\<close>));
\<close>

(* a type variable inside the term: LK3 against the stock twin LK3h; LK3d copies the shown term *)
locale Parent3 = fixes f :: "nat \<Rightarrow> 'b" and n :: nat and y :: 'b defines "y \<equiv> f n"
light_locale LK3 = Parent3 f "card UNIV" _ for f
locale LK3h = Parent3 f "card UNIV" _ for f
light_locale LK3d = Parent3 f "card UNIV" "f (card UNIV)" for f
context LK3h begin
ML \<open>val lk3h_y_def = Thm.prop_of @{thm y_def}\<close>
end
ML \<open>
val thy = \<^theory>;
fun rename_jointly ts =
  let val names = map #1 (tfrees ts); val fresh = map (fn i => "'r" ^ string_of_int i) (1 upto length names)
  in map (Term.map_types (Term.map_type_tfree (fn (a, S) => TFree (nth fresh (the (AList.lookup (op =) (names ~~ (0 upto length names - 1)) a)), S)))) ts end;
val heavy_n_y =
  let val [_, nh, _] = instances thy "Parent3" (loc thy "LK3h"); val yh = #2 (Logic.dest_equals lk3h_y_def)
  in rename_jointly [nh, yh] end;
fun check l =
  let
    val insts as [_, n, y] = instances thy "Parent3" (loc thy l);
    val _ = \<^assert> (length (tfrees insts) = 2);
    val _ = \<^assert> (eq_list (op aconv) (rename_jointly [n, y], heavy_n_y));
  in () end;
val _ = check (loc thy "LK3"); val _ = check (loc thy "LK3d");
\<close>

(* a conflict from a parameter shared through for: stock's type error, not a section-6 message *)
locale Nat_Fun = fixes f :: "'a \<Rightarrow> nat"
ML \<open>
val _ = fails_prefix "Type unification failed" (light \<^theory> "LC = Nat_Fun f + Parent f v \"(f v :: bool)\" for f v");
\<close>

(* defines and notes in a light header (plan lines 4999-5002): the four cases pin where the check
   runs, each with the section-6 text verbatim -- (a) the right-hand side mentions the eliminated
   name, (b) the left-hand side's head is not a parameter, (c) a short-name notes, (d) the benign
   forms that would reach eval *)
locale HB = fixes a :: nat assumes hb: "a = a"
lemma (in HB) hthm: "a + 0 = a" by simp
ML \<open>
val defines_text = "A light locale does not support `defines` clauses";
val notes_text = "A light locale does not support `notes` clauses";
val _ = fails_with defines_text (light \<^theory> "LX = Parent f v _ for f v + fixes q :: 'b defines \"q \<equiv> y\"");
val _ = fails_with defines_text (light \<^theory> "LX = Parent f v _ for f v + defines \"q \<equiv> f v\"");
val _ = fails_with notes_text (light \<^theory> "LX = HB + notes h = hthm");
val _ = fails_with defines_text (light \<^theory> "LX = Parent f v _ for f v + fixes q :: 'b defines \"q \<equiv> f v\"");
val _ = fails_with notes_text (light \<^theory> "LX = HB + assumes ax: \"a = a\" notes h = conjI [OF ax]");
\<close>

(* the D20 declaration warning: single source, two sources *)
locale X1 = fixes f :: "nat \<Rightarrow> nat" and a b :: nat defines "a \<equiv> f b"
locale X2 = fixes g :: "nat \<Rightarrow> nat" and b c :: nat defines "b \<equiv> g c"
ML \<open>
val _ = \<^assert> (declares \<^theory> "LD1 = Parent f v _ for f v" =["The following definitions from `Parent` are unfolded.\n  y \<equiv> f v\nThe names `y` are not bound and shouldn't be used any more. Write their unfolded terms instead."]);
val _ = \<^assert> (declares \<^theory> "LD2 = X1 + X2" =["The following definitions from `X1` are unfolded.\n  a \<equiv> f b\nThe following definitions from `X2` are unfolded.\n  b \<equiv> g c\nThe names `a` are not bound and shouldn't be used any more. Write their unfolded terms instead."]);
\<close>

end
