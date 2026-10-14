(* Sibling S2b: a second syntax-only registration of the same instance under Q. *)
theory Test5_Merge_S2b
  imports Test5_Merge_T0
begin

interpretation Q: LF t by unfold_locales simp

end
