(* Plan section 7 test 5 (external use and propagation): a general instance upgraded by a later plain path.  H7 = LF a + K + HB a for a: interpretation I: H7 x for x fails loudly with Duplicate fact declaration (the message starts with it; the fact that clashes depends on the fixture).  H9 = LF a + B: K + HB a for a succeeds with I.B.hb present; a later abbreviation (in HB) reaches I. and I.B. once each. *)
theory Test5_H7
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
consts c :: nat
light_locale LF = HB
locale K = HB c
locale H7 = LF a + K + HB a for a

ML \<open>
val _ = fails_prefix "Duplicate fact declaration" (fn () => interpretation_cmd "I: H7 x for x" \<^theory>);
\<close>

locale H9 = LF a + B: K + HB a for a
interpretation I: H9 x for x by unfold_locales simp_all
abbreviation (in HB) hba9 where "hba9 \<equiv> x + 2"

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_H7.I." =
  ["Test5_H7.I.B.HB_axioms", "Test5_H7.I.B.HP_axioms", "Test5_H7.I.B.K_axioms", "Test5_H7.I.B.hb",
   "Test5_H7.I.B.hp", "Test5_H7.I.B.hpl", "Test5_H7.I.H9_axioms", "Test5_H7.I.HB_axioms",
   "Test5_H7.I.HP_axioms", "Test5_H7.I.LF_axioms", "Test5_H7.I.hb", "Test5_H7.I.hp", "Test5_H7.I.hpl"]);
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "hba9" =
  ["Test5_H7.HB.hba9", "Test5_H7.I.B.hba9", "Test5_H7.I.hba9"]);
\<close>

end
