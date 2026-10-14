(* Plan section 7 test 5 (external use and propagation): the variant with interpretation J: K in the middle succeeds on the light side (K's theorem goes under J). *)
theory Test5_Cross_J
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  t :: nat  t1 :: nat  t2 :: nat
light_locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation J: K by unfold_locales simp_all
interpretation I: HB x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_J.I." =
  ["Test5_Cross_J.I.HB_axioms", "Test5_Cross_J.I.LF_axioms", "Test5_Cross_J.I.hb"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_J.J." =
  ["Test5_Cross_J.J.HB_axioms", "Test5_Cross_J.J.K_axioms", "Test5_Cross_J.J.hb"]);
\<close>

end
