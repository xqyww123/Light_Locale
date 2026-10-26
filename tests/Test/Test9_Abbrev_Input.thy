(* Plan section 7 test 9 (structure), plan 5106: the (input) abbreviation does not fold, the bare
   operator prints bare (a leaf of its own: Test9_Abbrev's Pu would fold here). *)
theory Test9_Abbrev_Input
  imports Test9_Fixtures
begin

context LF
begin

abbreviation (input) Pv where "Pv \<equiv> UP S"

ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.reads ctxt "x \<otimes>\<^bsub>Pv\<^esub> y" aconv Test_Support.reads ctxt "x \<otimes> y");
val _ = Test_Support.prints_as ctxt "x \<otimes> y" "x \<otimes> y";
in end\<close>

end

end
