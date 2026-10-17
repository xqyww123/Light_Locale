(* Plan section 7 test 9 (structure), plan 5303: only one sibling sets a value -- the other
   import order. *)
theory Test9_Sib_A0_A
  imports Test9_Sib_A0 Test9_Sib_A
begin

context LF
begin
ML_val \<open>\<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "S"))\<close>
end

end
