(* Plan section 7 test 9 (structure), plan 5302-5303: two siblings set different values; the
   first import wins (merge_options). *)
theory Test9_Sib_AB
  imports Test9_Sib_A Test9_Sib_B
begin

context LF
begin
ML_val \<open>\<^assert> (Test_Support.implicit_is \<^context> (Test_Support.reads \<^context> "S"))\<close>
end

end
