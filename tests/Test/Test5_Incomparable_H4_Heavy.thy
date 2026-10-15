(* The heavy twin of Test5_Incomparable's qualified row (plan lines 4145-4148): with locale
   LFh = HB, H4h = LFh a + A: K + B: K2 for a succeeds and the general instance prunes both special
   ones -- exactly one I.hb (the general ?x = ?x) and no I.A.hb / I.B.hb. *)
theory Test5_Incomparable_H4_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"

consts c :: nat  d :: nat
locale LFh = HB
locale K = HB c
locale K2 = HB d
locale H4h = LFh a + A: K + B: K2 for a
interpretation I: H4h x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Incomparable_H4_Heavy.I." =
  ["Test5_Incomparable_H4_Heavy.I.A.K_axioms", "Test5_Incomparable_H4_Heavy.I.B.K2_axioms",
   "Test5_Incomparable_H4_Heavy.I.H4h_axioms", "Test5_Incomparable_H4_Heavy.I.HB_axioms",
   "Test5_Incomparable_H4_Heavy.I.LFh_axioms", "Test5_Incomparable_H4_Heavy.I.hb"]);
val _ = \<^assert> (Thm.prop_of @{thm I.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
(*the fixture pin: the pruned special instances are invisible to the assertions above*)
val _ = \<^assert> (eq_list (op aconv) (instances \<^theory> "HB" (loc \<^theory> "K"), [\<^term>\<open>c\<close>])
  andalso eq_list (op aconv) (instances \<^theory> "HB" (loc \<^theory> "K2"), [\<^term>\<open>d\<close>]));
\<close>

end
