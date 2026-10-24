(* Plan section 7 test 9 (structure): the two guards of set_implicit_structure and
   with_implicit_structure (plan section 4 item 6; rows at plan 5263).  The block rows run in an
   unnamed block fixing p :: int -- no type variable is declared there, so the names the messages
   print are 'a, 'b, 'c (a locale's block cannot set the implicit structure since the ban of
   2026-10-23; the header's guard is Test9_Header_Implicit row 12).  Every row drives the
   command's function: the negative rows through fails_checked -- the ten verbatim rows compare
   the whole text with the approved texts of plan section 6 and the 'z row of plan 3677
   (fails_with), the nine structural rows (s1)-(s9) assert substrings only -- and the two
   positive rows through can. *)
theory Test9_Guards
  imports Test9_Fixtures
begin

consts pq :: "int \<Rightarrow> int"

ML \<open>
open Test_Support;

fun set_in lthy text = fn () => Light_Locale.set_implicit_structure_cmd text lthy;
fun with_in ctxt text = fn () => Light_Locale.with_implicit_structure_cmd text ctxt;

val record = "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>";
(*the bare record expression has two type variables -- the carrier's and the operations' --
  (partial_object_ext UNIV (monoid_ext (+) 0 ())); the annotation makes it the 'a monoid of the
  approved text (a bare 'a would stop earlier, at stock's sort constraint check)*)
val record_input = record ^ " :: 'a::{plus,zero} monoid";
val record_msg =
  "Undeclared type variable 'a in the implicit structure `" ^ record ^
  "`, where `0 :: 'a::{plus,zero}` requires a concrete type annotation.";

(*a structural row: the message of the failing value satisfies the predicate (through
  fails_checked: an accepted value fails the row)*)
fun structural lthy text describe check = fails_checked describe check (set_in lthy text);
\<close>

context
  fixes p :: int
begin

ML_val \<open>
val lthy = \<^context>;

(*the verbatim rows of plan section 6; the tenth, the 'z row, ends the block*)
val _ = fails_with record_msg (set_in lthy record_input);
(*the bare record: its carrier and its operations are two undeclared type variables (plan section
  11 (32)(a); the text approved 2026-10-16)*)
val _ =
  fails_with
    ("Undeclared type variables 'a, 'b in the implicit structure `" ^ record ^
      "`, where `UNIV :: 'a set` and `0 :: 'b::{plus,zero}` require concrete type annotations.")
    (set_in lthy record);
val _ =
  fails_with
    "Undeclared type variables 'a, 'b in the implicit structure `(UNIV, 0)`, where `UNIV :: 'a set` and `0 :: 'b::zero` require concrete type annotations."
    (set_in lthy "(UNIV, 0)");
val _ =
  fails_with
    "Undeclared type variables 'a, 'b in the implicit structure `undefined`, where `undefined :: 'a \<Rightarrow> 'b` requires a concrete type annotation."
    (set_in lthy "undefined :: 'a \<Rightarrow> 'b");
val _ =
  fails_with
    "Undeclared type variables 'a, 'b, 'c in the implicit structure `(UNIV, 0, undefined)`, where `UNIV :: 'a set`, `0 :: 'b::zero` and `undefined :: 'c` require concrete type annotations."
    (set_in lthy "(UNIV, 0, undefined)");
val _ =
  fails_with
    "Undeclared type variable 'a in the implicit structure `\<lambda>x. x`, where `x :: 'a` requires a concrete type annotation."
    (set_in lthy "\<lambda>x. x");
val _ =
  fails_with
    "Undeclared type variables 'a, 'b in the implicit structure `\<lambda>x. 0`, where `x :: 'a` and `0 :: 'b::zero` require concrete type annotations."
    (set_in lthy "\<lambda>x. 0");
val _ =
  fails_with
    "Undeclared type variables 'a, 'b in the implicit structure `\<lambda>_. 0`, where `_ :: 'a` and `0 :: 'b::zero` require concrete type annotations."
    (set_in lthy "\<lambda>_. 0");

(*the structural rows (s1)-(s9), plan 5263*)
val has = String.isSubstring;
val _ = structural lthy (record ^ "\<lparr>one := 1\<rparr>") "s1: a number carries 'a, no hidden binder" (fn s =>
  not (has "`_ :: " s) andalso not (has "uu" s) andalso (has "where `1 :: " s orelse has "where `0 :: " s));
val _ = structural lthy "\<lambda>x. x + 0" "s2: the used binder before the number" (fn s =>
  has "`x :: " s andalso not (has "`0 :: " s));
val _ = structural lthy "\<lambda>x::'a. (UNIV::'a set)" "s3: the constant before the unused binder" (fn s =>
  has "`UNIV :: 'a set`" s andalso not (has "`x :: " s));
val _ = structural lthy "\<lambda>(x::'a) (y::'a). y" "s4: the used binder y, not x" (fn s =>
  has "`y :: " s andalso not (has "`x :: " s));
val _ = structural lthy "\<lambda>x. undefined (\<lambda>x. x)" "s5: the renamed inner binder" (fn s =>
  has "\<lambda>xa. xa" s andalso has "`x :: " s andalso has "`xa :: " s);
val _ = structural lthy "\<lambda>x. undefined x" "s7: no eta contraction" (fn s =>
  has "`\<lambda>x. undefined x`" s andalso has "`x :: " s);
val _ = structural lthy "- 3" "s8: a negative number" (fn s => has "`- 3 :: " s andalso not (has "~" s));
val _ = structural lthy "{(x, 0) | x. True}" "s9: the comprehension's hidden binder" (fn s =>
  has "`x :: " s andalso has "`0 :: " s andalso not (has "uu" s));
(*a type variable the user wrote but did not declare (plan 3677): the same text; the operations'
  type variable is undeclared beside it, since the bare record does not tie the two -- measured
  2026-10-16, text approved the same day as an instance of the approved template*)
val _ =
  fails_with
    "Undeclared type variables 'z, 'a in the implicit structure `\<lparr>carrier = UNIV, mult = (*), one = 1\<rparr>`, where `UNIV :: 'z::comm_ring_1 set` and `1 :: 'a::{one,times}` require concrete type annotations."
    (set_in lthy "\<lparr>carrier = (UNIV :: 'z::comm_ring_1 set), mult = (*), one = 1\<rparr>");
\<close>

context
  fixes x :: nat
begin
ML_val \<open>
val lthy = \<^context>;
(*(s6): the avoidance set is the printer's, not the context's names -- x is not renamed*)
val _ = structural lthy "\<lambda>x. x" "s6: x not renamed although fixed outside" (fn s =>
  String.isSubstring "`\<lambda>x. x`" s andalso String.isSubstring "`x :: 'a`" s);
(*the guards run in a nested block too: it reports the first verbatim text*)
val _ = fails_with record_msg (set_in lthy record_input);
(*the free variable guard: the variables fixed in the block, outer first*)
val _ =
  fails_with
    "Illegal undeclared variable \"q\" in the implicit structure. Only variables fixed in this context may occur here: \"p\", \"x\"."
    (set_in lthy "pq q");
\<close>
end

end


subsection \<open>with_implicit_structure: the same guards, the non-locale sentence (plan 5263)\<close>

lemma "(0 :: int) = 0"
proof -
  ML_prf \<open>
    val ctxt = \<^context>;
    val _ = fails_with record_msg (with_in ctxt record_input);
    val _ =
      fails_with
        "Illegal undeclared variable \"q\" in the implicit structure. No variables are fixed in this context, so no variable may occur here."
        (with_in ctxt "pq q");
    val _ = \<^assert> (can (with_in ctxt (record ^ " :: int monoid")) ());
  \<close>
  fix y :: int
  ML_prf \<open>val _ = \<^assert> (can (with_in \<^context> "pq y") ())\<close>
  (*the proof's y is listed by its external name; the term carries its skolem name*)
  ML_prf \<open>
    val _ =
      fails_with
        "Illegal undeclared variable \"q\" in the implicit structure. Only variables fixed in this context may occur here: \"y\"."
        (with_in \<^context> "pq q");
  \<close>
  fix G
  ML_prf \<open>
    val _ =
      fails_with
        "Undeclared type variable 'a in the implicit structure `G`, where `G :: 'a` requires a concrete type annotation."
        (with_in \<^context> "G");
  \<close>
  (*a second fix of y gives another skolem name; the list names y once*)
  fix y :: int
  ML_prf \<open>
    val _ =
      fails_with
        "Illegal undeclared variable \"q\" in the implicit structure. Only variables fixed in this context may occur here: \"y\", \"G\"."
        (with_in \<^context> "pq q");
  \<close>
  show ?thesis ..
qed

context LF
begin
lemma "True"
proof -
  ML_prf \<open>
    (*a proof opened from a locale's block may set the proof's implicit structure; the value is
      checked against the proof's variables, so the sentence lists S*)
    val _ =
      fails_with
        "Illegal undeclared variable \"q\" in the implicit structure. Only variables fixed in this context may occur here: \"S\"."
        (with_in \<^context> "pq q");
  \<close>
  show True ..
qed
end

end
