(* Plan section 7 test 9 (structure), plan 5303: only one sibling sets a value -- both import
   orders get it. *)
theory Test9_Sib_A_A0
  imports Test9_Sib_A Test9_Sib_A0
begin

context LF
begin
ML_val \<open>\<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "S"))\<close>
end

end
