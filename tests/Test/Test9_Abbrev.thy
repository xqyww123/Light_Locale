(* Plan section 7 test 9 (structure), plan 5105: an abbreviation whose right-hand side is the
   implicit structure folds the index argument; the stored value, put through the uncheck stages
   before the comparison, folds the same way, so the subscript is elided (section 11 (39); the
   abbreviation is stored in LF: own leaf). *)
theory Test9_Abbrev
  imports Test9_Fixtures
begin

context LF
begin

abbreviation Pu where "Pu \<equiv> UP S"

ML_val \<open>
open Test_Support;
val ctxt = \<^context>;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S"));
(*the value folds to Pu, so the row tells the uncheck stages apart*)
val _ = prints_as ctxt "UP S" "Pu";
val _ = prints_as ctxt "x \<otimes> y" "x \<otimes> y";
val _ = \<^assert> (round_trips ctxt (reads ctxt "x \<otimes> y"));
val _ = \<^assert> (shows (Config.put show_markup true ctxt) (reads ctxt "x \<otimes> y") = "x \<otimes> y");
(*the abbreviation written as the subscript reads as the same term (decision 16 (a))*)
val _ = \<^assert> (reads ctxt "x \<otimes>\<^bsub>Pu\<^esub> y" aconv reads ctxt "x \<otimes> y");
\<close>

end

end
