(* Plan section 7 test 9 (structure), plan 5263: the guards accept a closed monomorphic record and
   a term of the parameter's type variables -- own fixture LFtg, whose slot these rows write. *)
theory Test9_Guards_Positive
  imports Test9_Fixtures
begin

light_locale LFtg = monoid G for G

context LFtg
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
ML_val \<open>
\<^assert> (Test_Support.implicit_is \<^context>
  (Test_Support.reads \<^context> "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"))
\<close>
set_implicit_structure "f G"
ML_val \<open>\<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "f G"))\<close>
end

end
