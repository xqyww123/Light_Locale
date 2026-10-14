(* Plan section 7 test 5 (external use and propagation), restocking after H8 = LF a + HB a + K for a
   (Light side): after interpretation I: H8 x for x, definition (in HB) d reaches I. exactly once. *)
theory Test5_Restock_H8
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
consts c :: nat
light_locale LF = HB
locale K = HB c
locale H8 = LF a + HB a + K for a

interpretation I: H8 x for x by unfold_locales simp_all

definition (in HB) d where "d = x"

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (consts_named ctxt "d" = ["Test5_Restock_H8.HB.d", "Test5_Restock_H8.I.d"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H8.I." =
  ["Test5_Restock_H8.I.H8_axioms", "Test5_Restock_H8.I.HB_axioms", "Test5_Restock_H8.I.HP_axioms", "Test5_Restock_H8.I.K_axioms",
   "Test5_Restock_H8.I.LF_axioms", "Test5_Restock_H8.I.d_def", "Test5_Restock_H8.I.hb", "Test5_Restock_H8.I.hp", "Test5_Restock_H8.I.hpl"]);
val _ = \<^assert> (Thm.prop_of @{thm I.hb} aconv Logic.varify_global \<^prop>\<open>(x::nat) = x\<close>);
\<close>

end
