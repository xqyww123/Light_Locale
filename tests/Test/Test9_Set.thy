(* Plan section 7 test 9 (structure): set_implicit_structure (plan decision 16 (d); rows at plan
   5280-5293 and 5250-5253).  Block scope first, while no slot is written: the nested block, the
   unnamed theory-level block, the theory top level, the free variable guard in the locale
   branch.  Then the slot rows on the heavy D and the light LF: the next command, the reopened
   block, lemma (in ..), children declared before and after, three values in a row, and the
   typed rows of a re-declared value. *)
theory Test9_Set
  imports Test9_Fixtures
begin

consts g2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"

ML \<open>
open Test_Support;
val lf = Named_Target.init [] (loc \<^theory> "LF") \<^theory>;
val guard_locale =
  "Illegal free variables in the implicit structure: \"q\". Only the parameters of locale \"LF\" may occur here.";
\<close>


subsection \<open>Block scope (plan 5285-5289)\<close>

context LF
begin
context
begin
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "UP S"))\<close>
end

context LF
begin
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
val top_level =
  "You cannot set the implicit structure at the theory level. Use it inside a locale or a context block.";
val _ =
  fails_with top_level
    (fn () => Light_Locale.set_implicit_structure_cmd "undefined" (Named_Target.theory_init \<^theory>));
\<close>
(*the level is judged before the value is read: a bare index position, unreadable here, still
  gets the theory-level text (a block of its own: a row of the restore plan's mutation checks)*)
ML \<open>
val _ =
  fails_with top_level
    (fn () => Light_Locale.set_implicit_structure_cmd "x \<otimes> y" (Named_Target.theory_init \<^theory>));
\<close>


subsection \<open>The free variable guard in the locale branch (plan 5289-5293)\<close>

ML \<open>
val _ = fails_with guard_locale (fn () => Light_Locale.set_implicit_structure_cmd "UP q" lf);
val _ =
  fails_with
    "Illegal free variables in the implicit structure: \"q\", \"r\". Only the parameters of locale \"LF\" may occur here."
    (fn () => Light_Locale.set_implicit_structure_cmd "UP (g2 q r)" lf);
(*only the fails_with rows carry the guard: a failed command leaves lf as it was by the context
  model itself; the fixture check below only pins what lf is*)
val _ = \<^assert> (is_none (Syntax_Trans.default_struct lf) andalso implicit_is lf (reads lf "UP S"));
\<close>
locale LFc_after_guard = LF
ML \<open>\<^assert> (implicit_is (Locale.init (loc \<^theory> "LFc_after_guard") \<^theory>) (reads lf "UP S"))\<close>


subsection \<open>The slot of the heavy D and of the light LF (plan 5280-5284)\<close>

locale Dc0 = D
locale LFc0 = LF

context D
begin
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
context D
begin
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
lemma (in D) "True"
  ML_prf \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close> ..

context LF
begin
set_implicit_structure "S"
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
context LF
begin
ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close>
end
lemma (in LF) "True"
  ML_prf \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "S"))\<close> ..

locale Dc1 = D
locale LFc1 = LF
ML \<open>
val thy = \<^theory>;
fun opened name = Locale.init (loc thy name) thy;
val _ = List.app (fn name => \<^assert> (implicit_is (opened name) (reads (opened name) "S")))
  ["Dc0", "Dc1", "LFc0", "LFc1"];
\<close>

(* three values in a row: the one value changes (plan 5284) *)
context LF
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
end


subsection \<open>A re-declared value changes the placeholder's type (plan 5250-5253)\<close>

context LF
begin
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
