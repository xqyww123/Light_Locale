(* Plan section 7 test 9 (structure), plan 5302-5303 as the ban of 2026-10-23 leaves them: the two
   siblings' copies of LS differ in their dynamic parts, so the merge goes through merge_locale,
   which keeps the header's S (the static part of the first copy) and both abbreviations (the
   dynamic parts merged).  A merge that wrote Inherit into the slot would open LS with the cut UP S. *)
theory Test9_Sib_AB
  imports Test9_Sib_A Test9_Sib_B
begin

context LS
begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "S"));
val _ = \<^assert> (Test_Support.reads ctxt "sib_a" aconv Test_Support.reads ctxt "S");
val _ = \<^assert> (Test_Support.reads ctxt "sib_b" aconv Test_Support.reads ctxt "S");
\<close>
end

end
