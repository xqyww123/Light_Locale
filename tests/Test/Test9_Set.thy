(* Plan section 7 test 9 (structure): set_implicit_structure (plan decision 16 (d); rows at plan
   5280-5293 and 5250-5253, as the ban of 2026-10-23 leaves them: no block whose bottom target is
   a locale sets the implicit structure; a locale's is declared in its header).  Block scope in
   unnamed blocks: the nested block, the theory top level.  The ban: the heavy D, the light LF, a
   class, a block nested in one of their blocks; it is judged before the value is read; a block
   whose bottom target is neither the theory nor a locale (overloading) accepts the command.  Then
   three values in a row and the typed rows of a re-declared value, in an unnamed block fixing S. *)
theory Test9_Set
  imports Test9_Fixtures
begin

consts g2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"

ML \<open>
open Test_Support;
val inside_locale =
  "You cannot set the implicit structure inside a locale. Declare it in the header of a light locale with implicit_structure instead.";
val top_level =
  "You cannot set the implicit structure at the theory level. Use it inside a context block.";
fun set_in lthy text = fn () => Light_Locale.set_implicit_structure_cmd text lthy;
\<close>


subsection \<open>Block scope in unnamed blocks (plan 5285-5289)\<close>

context
  fixes S :: "('a, 'b) ring_scheme"
begin
context
begin
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
ML_val \<open>\<^assert> (is_none (Syntax_Trans.implicit_structure \<^context>))\<close>
set_implicit_structure "UP S"
context
begin
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "UP S"))\<close>
end

context
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"));
val _ = \<^assert> (bare_denotes ctxt "\<lparr>carrier = UNIV, mult = (+), one = (0 :: int)\<rparr>");
\<close>
end

ML \<open>
val _ = \<^assert> (is_none (Syntax_Trans.implicit_structure \<^context>));
val _ = fails_with top_level (set_in (Named_Target.theory_init \<^theory>) "undefined");
\<close>
(*the level is judged before the value is read: a bare index position, unreadable here, still
  gets the theory-level text (a block of its own: a row of the restore plan's mutation checks)*)
ML \<open>
val _ = fails_with top_level (set_in (Named_Target.theory_init \<^theory>) "x \<otimes> y");
\<close>


subsection \<open>The ban: no block of a locale sets the implicit structure\<close>

(* judged before the value is read: a value the guard would refuse (UP q), one that does not
   parse, the blank value and a good value all get the one text *)
ML \<open>
val lf = Named_Target.init [] (loc \<^theory> "LF") \<^theory>;
val _ = List.app (fn text => fails_with inside_locale (set_in lf text)) ["UP q", "(", "", "S"];
\<close>

(* the heavy D and the light LF, each with a block nested in its block; a class *)
context D
begin
ML_val \<open>fails_with inside_locale (set_in \<^context> "S")\<close>
context
begin
ML_val \<open>fails_with inside_locale (set_in \<^context> "S")\<close>
end
end
context LF
begin
ML_val \<open>fails_with inside_locale (set_in \<^context> "S")\<close>
context
  fixes x :: nat
begin
ML_val \<open>fails_with inside_locale (set_in \<^context> "S")\<close>
end
end
class C = fixes G :: "'a monoid"
context C
begin
ML_val \<open>fails_with inside_locale (set_in \<^context> "G")\<close>
end

(* a block whose bottom target is neither the theory nor a locale -- overloading here -- accepts
   the command, and the value stays inside the block (the ban covers locale and class blocks only) *)
overloading g2_nat \<equiv> "g2 :: nat \<Rightarrow> nat \<Rightarrow> nat"
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"))\<close>
definition g2_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "g2_nat x y = x + y"
end
ML \<open>\<^assert> (is_none (Syntax_Trans.implicit_structure \<^context>))\<close>


subsection \<open>Three values in a row (plan 5284); a re-declared value changes the placeholder's type (plan 5250-5253)\<close>

context
  fixes S :: "('a, 'b) ring_scheme"
begin
set_implicit_structure "UP S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "UP S"))\<close>
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
set_implicit_structure "UP S"
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S"));
val _ = \<^assert> (fastype_of (reads ctxt "x \<otimes> y") = \<^typ>\<open>nat \<Rightarrow> 'a\<close>);
\<close>

set_implicit_structure "S"
ML_val \<open>
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>S\<^esub> y");
val _ = \<^assert> (can (Thm.cterm_of ctxt) t);
\<close>
set_implicit_structure "UP S"
ML_val \<open>
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>UP S\<^esub> y");
val _ = \<^assert> (can (Thm.cterm_of ctxt) t);
\<close>
set_implicit_structure "S"
ML_val \<open>
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>S\<^esub> y");
val _ = \<^assert> (can (Thm.cterm_of ctxt) t);
\<close>
set_implicit_structure "UP S"
ML_val \<open>
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>UP S\<^esub> y");
val _ = \<^assert> (can (Thm.cterm_of ctxt) t);
val _ = \<^assert> (fastype_of t = \<^typ>\<open>nat \<Rightarrow> 'a\<close>);
\<close>
lemma "True"
proof -
  with_implicit_structure "S"
  ML_prf \<open>
    val ctxt = \<^context>;
    val t = reads ctxt "x \<otimes> y";
    val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>S\<^esub> y");
    val _ = \<^assert> (can (Thm.cterm_of ctxt) t);
  \<close>
  show True ..
qed
end

end
