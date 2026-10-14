(* Sibling S1: the syntax-only registration of HB t under I. *)
theory Test5_Merge_S1
  imports Test5_Merge_T0
begin

interpretation I: LF t by unfold_locales simp

end
