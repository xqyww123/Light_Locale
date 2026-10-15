(* The heavy twin of Test5_Incomparable's failure rows (plan lines 4139-4144): locale LFh = HB and
   LF2h = HB c in place of the light ones.  The special-instance-first H1h and the two-path H2h
   declare and their interpretations fail the same way as on the light side (Duplicate fact
   declaration quoting I1.HB_axioms / I2.HB_axioms -- here two Full copies); H3h = LFh a + K + K2 for a with interpretation I: H3h x for x
   succeeds, the general instance pruning both special ones -- exactly one I.hb, the general
   theorem ?x = ?x. *)
theory Test5_Incomparable_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  d :: nat
locale LFh = HB
locale LF2h = HB c
locale K = HB c
locale K2 = HB d
locale H1h = K + LFh a for a
locale H2h = LF2h + LFh a for a

ML \<open>
(*each quoting its clashing fact, as on the light side*)
val _ = List.app (fn (t, clash) =>
    fails_prefix ("Duplicate fact declaration \"Test5_Incomparable_Heavy." ^ clash ^ "\"")
      (fn () => interpretation_cmd t \<^theory>))
  [("I1: H1h x for x", "I1.HB_axioms"), ("I2: H2h x for x", "I2.HB_axioms")];
\<close>

locale H3h = LFh a + K + K2 for a
interpretation I: H3h x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Incomparable_Heavy.I." =
  ["Test5_Incomparable_Heavy.I.H3h_axioms", "Test5_Incomparable_Heavy.I.HB_axioms",
   "Test5_Incomparable_Heavy.I.K2_axioms", "Test5_Incomparable_Heavy.I.K_axioms",
   "Test5_Incomparable_Heavy.I.LFh_axioms", "Test5_Incomparable_Heavy.I.hb"]);
val _ = \<^assert> (Thm.prop_of @{thm I.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
(*the fixture pin: the general instance prunes the special ones whatever their arguments, so the
  assertions above would not notice a slip in K or K2*)
val _ = \<^assert> (eq_list (op aconv) (instances \<^theory> "HB" (loc \<^theory> "K"), [\<^term>\<open>c\<close>])
  andalso eq_list (op aconv) (instances \<^theory> "HB" (loc \<^theory> "K2"), [\<^term>\<open>d\<close>]));
\<close>

end
