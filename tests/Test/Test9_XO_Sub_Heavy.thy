(* Plan section 7 test 9 (structure), plan 5214-5215: the heavy twin of Test9_XO_Sub. *)
theory Test9_XO_Sub_Heavy
  imports Test9_Fixtures
begin

sublocale D \<subseteq> U: XO S "\<one>\<^bsub>UP S\<^esub>"
  by unfold_locales

ML \<open>
val insts = Test_Support.instances \<^theory> "XO" "D";
val _ = \<^assert> (not (exists Test_Support.has_placeholder insts));
\<close>

end
