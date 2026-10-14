(* Plan section 7 test 5 (external use and propagation), the sibling-theory layout (Light side), the
   declarations only: HB with the Plain lemma hb, the constants, LF, K, K4.  No registration here. *)
theory Test5_Sib_T0
  imports Test_Support
begin

locale HB = fixes x z :: nat assumes hbx: "x = x"
lemma (in HB) hb: "x + z = z + x" by simp
consts c :: nat  d :: nat
light_locale LF = HB x c for x
locale K = HB d c
locale K4 = HB x c for x

end
