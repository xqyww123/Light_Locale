(* Plan section 7 test 12, the merge group (A10): the other parent's entry. *)
theory Tab_B
  imports Tab_Fix
begin

interpretation J: LFs "{0::nat}" by (rule LFs.intro) simp

end
