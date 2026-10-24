(* Plan section 7 test 9 (structure), plan 5302-5303 as the ban of 2026-10-23 leaves them: the
   other import order -- the same header's S and both abbreviations after merge_locale. *)
theory Test9_Sib_BA
  imports Test9_Sib_B Test9_Sib_A
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
