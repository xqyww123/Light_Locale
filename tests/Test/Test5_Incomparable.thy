(* Plan section 7 test 5 (external use and propagation), plan lines 4139-4147 on the light side
   (family 5, plan line 4148, is Test5_Incomparable_F5).  With K = HB c and K2 = HB d: the special
   instance first (H1 = K + LF a for a), two light paths (LF2 = HB c, H2 = LF2 + LF a for a) and
   two incomparable special instances (H3 = LF a + K + K2 for a) all declare, and their
   interpretations fail loudly (Duplicate fact declaration, quoting the clashing fact: for H1
   I1.HB_axioms, the Full copy from K's HB c and the syntax-only copy from LF's light edge HB ?x;
   for H2 I2.HB_axioms, the two syntax-only copies from the light edges of LF2 (HB c) and of LF
   (HB ?x), plan line 3534; for H3 I3.hb, the Plain hb of the two Full instances HB c and HB d,
   plan line 4144) -- H1 and H2 like the
   heavy twin, H3 where the heavy twin succeeds (Test5_Incomparable_Heavy); the qualified
   H4 = LF a + A: K + B: K2 for a succeeds with I.A.hb: c = c, I.B.hb: d = d, the two HB_axioms
   carrying the import qualifiers A and B, the light edge's I.HB_axioms: HB ?x and no general
   I.hb. *)
theory Test5_Incomparable
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"

consts c :: nat  d :: nat
light_locale LF = HB
light_locale LF2 = HB c
locale K = HB c
locale K2 = HB d
locale H1 = K + LF a for a
locale H2 = LF2 + LF a for a
locale H3 = LF a + K + K2 for a

ML \<open>
(*the interpretations fail loudly, each quoting its clashing fact*)
val _ = List.app (fn (t, clash) =>
    fails_prefix ("Duplicate fact declaration \"Test5_Incomparable." ^ clash ^ "\"")
      (fn () => interpretation_cmd t \<^theory>))
  [("I1: H1 x for x", "I1.HB_axioms"), ("I2: H2 x for x", "I2.HB_axioms"), ("I3: H3 x for x", "I3.hb")];
\<close>

locale H4 = LF a + A: K + B: K2 for a
interpretation I: H4 x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Incomparable.I." =
  ["Test5_Incomparable.I.A.HB_axioms", "Test5_Incomparable.I.A.K_axioms", "Test5_Incomparable.I.A.hb",
   "Test5_Incomparable.I.B.HB_axioms", "Test5_Incomparable.I.B.K2_axioms", "Test5_Incomparable.I.B.hb",
   "Test5_Incomparable.I.H4_axioms", "Test5_Incomparable.I.HB_axioms", "Test5_Incomparable.I.LF_axioms"]);
val _ = \<^assert> (Thm.prop_of @{thm I.A.hb} aconv \<^prop>\<open>c = c\<close>);
val _ = \<^assert> (Thm.prop_of @{thm I.B.hb} aconv \<^prop>\<open>d = d\<close>);
val _ = \<^assert> (Thm.prop_of @{thm I.HB_axioms} aconv Logic.varify_global \<^prop>\<open>HB x\<close>);
\<close>

end
