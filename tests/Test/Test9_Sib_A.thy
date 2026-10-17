(* Plan section 7 test 9 (structure), plan 5302-5303: sibling merge -- this sibling sets LF's
   slot to S. *)
theory Test9_Sib_A
  imports Test9_Fixtures
begin

context LF
begin
set_implicit_structure "S"
end

end
