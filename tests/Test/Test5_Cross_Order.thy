(* Plan section 7 test 5 (external use and propagation): the order I: LF, I: HB, I: K succeeds on the light side. *)
theory Test5_Cross_Order
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  t :: nat  t1 :: nat  t2 :: nat
light_locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation I: HB x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_Order.I." =
  ["Test5_Cross_Order.I.HB_axioms", "Test5_Cross_Order.I.K_axioms", "Test5_Cross_Order.I.LF_axioms", "Test5_Cross_Order.I.hb"]);
\<close>

end
