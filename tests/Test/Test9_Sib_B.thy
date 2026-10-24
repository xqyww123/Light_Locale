(* Plan section 7 test 9 (structure), plan 5302-5303 as the ban of 2026-10-23 leaves them: the
   other sibling changes LS's dynamic part with its own abbreviation and sees the header's S. *)
theory Test9_Sib_B
  imports Test9_Fixtures
begin

abbreviation (in LS) sib_b :: "('a, 'b) ring_scheme" where "sib_b \<equiv> S"

context LS
begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "S"));
val _ = \<^assert> (Test_Support.reads ctxt "sib_b" aconv Test_Support.reads ctxt "S");
\<close>
end

end
