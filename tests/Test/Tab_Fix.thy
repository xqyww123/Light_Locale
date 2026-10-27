(* Plan section 7 test 12 (repair phase, step 1), the merge of the predicate fact table (master
   plan lines 5353-5363; batch-1 plan section 4.1, A10): the fixture of the five-theory group, no
   interpretation. *)
theory Tab_Fix
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"

end
