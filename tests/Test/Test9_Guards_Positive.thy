(* Plan section 7 test 9 (structure), plan 5263: the guards accept a closed monomorphic record and
   a term of the fixed variable's type variables, in an unnamed block (a locale's block cannot set
   the implicit structure since the ban of 2026-10-23; the header's guard is Test9_Header_Implicit
   row 12). *)
theory Test9_Guards_Positive
  imports Test9_Fixtures
begin

context
  fixes G :: "('a, 'b) monoid_scheme"
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
ML \<open>
val _ = \<^assert> (Test_Support.implicit_is \<^context>
  (Test_Support.reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"))
\<close>
set_implicit_structure "f G"
ML \<open>val _ = \<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "f G"))\<close>
end

end
