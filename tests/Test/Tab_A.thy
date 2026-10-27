(* Plan section 7 test 12, the merge group (A10): one parent's entry. *)
theory Tab_A
  imports Tab_Fix
begin

interpretation I: LFs "{}::nat set" by (rule LFs.intro) simp

end
