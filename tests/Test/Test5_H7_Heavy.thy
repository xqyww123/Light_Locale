(* Plan section 7 test 5 (external use and propagation): the heavy twin of H7 (locale LF = HB): interpretation I: H7 x for x succeeds with exactly one I.hb: ?x = ?x. *)
theory Test5_H7_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
consts c :: nat
locale LF = HB
locale K = HB c
locale H7 = LF a + K + HB a for a
interpretation I: H7 x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_H7_Heavy.I." =
  ["Test5_H7_Heavy.I.H7_axioms", "Test5_H7_Heavy.I.HB_axioms", "Test5_H7_Heavy.I.HP_axioms",
   "Test5_H7_Heavy.I.K_axioms", "Test5_H7_Heavy.I.LF_axioms", "Test5_H7_Heavy.I.hb",
   "Test5_H7_Heavy.I.hp", "Test5_H7_Heavy.I.hpl"]);
val _ = \<^assert> (Thm.prop_of @{thm I.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
\<close>

end
