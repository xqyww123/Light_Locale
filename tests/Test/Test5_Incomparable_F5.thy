(* Plan section 7 test 5, family 5 (plan lines 4148-4149): A: K5a + B: K5b on its own constants and
   no general instance of HB.  It contains no light locale and no general instance, so this one
   stock run is the control for both sides: interpretation J: F5 gives J.A.hb, J.B.hb and the two
   HB_axioms carrying the import qualifiers A and B, and no general J.hb.  Its own leaf (plan line 3825): a Full general
   registration of HB earlier in the theory (in the first build, the one I: H4h leaves in
   Test5_Incomparable_H4_Heavy) would prune both instances, a syntax-only one would not (plan lines
   3536-3537; section 11 (31)). *)
theory Test5_Incomparable_F5
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"

consts c5 :: nat  d5 :: nat
locale K5a = HB c5
locale K5b = HB d5
locale F5 = A: K5a + B: K5b
interpretation J: F5 by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Incomparable_F5.J." =
  ["Test5_Incomparable_F5.J.A.HB_axioms", "Test5_Incomparable_F5.J.A.K5a_axioms", "Test5_Incomparable_F5.J.A.hb",
   "Test5_Incomparable_F5.J.B.HB_axioms", "Test5_Incomparable_F5.J.B.K5b_axioms", "Test5_Incomparable_F5.J.B.hb",
   "Test5_Incomparable_F5.J.F5_axioms"]);
\<close>

end
