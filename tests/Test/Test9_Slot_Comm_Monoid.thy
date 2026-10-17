(* Plan section 7 test 9 (structure), plan 5301: a slot on cring's second import only -- ring's
   surviving R arrives first, so cring opens with no implicit structure. *)
theory Test9_Slot_Comm_Monoid
  imports Test9_Fixtures
begin

context comm_monoid
begin
set_implicit_structure "f G"
end

ML \<open>
val thy = \<^theory>;
fun opened name = Locale.init (Test_Support.loc thy name) thy;
val _ = \<^assert> (Test_Support.implicit_is (opened "comm_monoid") (Test_Support.reads (opened "comm_monoid") "f G"));
val _ = \<^assert> (Test_Support.layers (opened "cring") = (SOME "R", NONE));
\<close>

end
