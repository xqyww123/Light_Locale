(* Sibling S2: the full interpretation of HB t under Q. *)
theory Test5_Merge_S2
  imports Test5_Merge_T0
begin

interpretation Q: HB t by unfold_locales simp

end
