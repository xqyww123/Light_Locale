(* Plan section 7 test 9 (structure), plan 5302-5303 as the ban of 2026-10-23 leaves them: a
   locale's implicit structure is declared in its header and lives in the static part of its
   record, which a theory merge takes from the first copy.  This sibling changes LS's dynamic part
   (an abbreviation goes through Locale.add_declaration) and sees the header's S, not the cut UP S. *)
theory Test9_Sib_A
  imports Test9_Fixtures
begin

abbreviation (in LS) sib_a :: "('a, 'b) ring_scheme" where "sib_a \<equiv> S"

context LS
begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "S"));
val _ = \<^assert> (Test_Support.reads ctxt "sib_a" aconv Test_Support.reads ctxt "S");
\<close>
end

end
