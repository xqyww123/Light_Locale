(* Plan section 7 test 5 (external use and propagation), the first emission after a pruned upgrade
   (heavy side): H5 = LF1 a + LF2 + M2 for a with heavy LF1 and LF2; the stock roundup prunes HP c
   under the general HP ?a, so I.hpl is the general instance.  definition (in HB) d reaches I.
   exactly once, as on the light side. *)
theory Test5_Restock_H5_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
consts c :: nat
locale LF1 = HP
locale LF2 = HB c
locale M2 = HB c
locale H5 = LF1 a + LF2 + M2 for a

interpretation I: H5 x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H5_Heavy.I." =
  ["Test5_Restock_H5_Heavy.I.H5_axioms", "Test5_Restock_H5_Heavy.I.HB_axioms",
   "Test5_Restock_H5_Heavy.I.HP_axioms", "Test5_Restock_H5_Heavy.I.LF1_axioms",
   "Test5_Restock_H5_Heavy.I.LF2_axioms", "Test5_Restock_H5_Heavy.I.M2_axioms",
   "Test5_Restock_H5_Heavy.I.hb", "Test5_Restock_H5_Heavy.I.hp", "Test5_Restock_H5_Heavy.I.hpl"]);
val _ = \<^assert> (Thm.prop_of @{thm I.hpl} aconv Logic.varify_global \<^prop>\<open>(x::nat) + 0 = x\<close>);
\<close>

definition (in HB) d where "d = x"

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" =
  ["Test5_Restock_H5_Heavy.HB.d", "Test5_Restock_H5_Heavy.I.d"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H5_Heavy.I.d" = ["Test5_Restock_H5_Heavy.I.d_def"]);
\<close>

end
