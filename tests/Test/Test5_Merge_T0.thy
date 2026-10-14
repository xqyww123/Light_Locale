(* Plan section 7 test 5 (external use and propagation), the theory merge of registrations: the
   declarations only. *)
theory Test5_Merge_T0
  imports Test_Support
begin

locale HB = fixes x :: nat assumes hb: "x = x"
consts t :: nat
light_locale LF = HB

end
