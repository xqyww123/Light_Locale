(* Plan section 7 test 9 (structure), plan 5302-5303: the other import order -- the first
   import wins. *)
theory Test9_Sib_BA
  imports Test9_Sib_B Test9_Sib_A
begin

context LF
begin
ML_val \<open>\<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "UP (UP S)"))\<close>
end

end
