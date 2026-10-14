(* Plan section 7 test 5 (external use and propagation), the first emission after a pruned upgrade
   (Light side): H5 = LF1 a + LF2 + M2 for a reaches HP ?a through LF1, HB c and HP c through LF2 and
   then, fully, through the heavy M2.  After interpretation I: H5 x for x, I.hpl is the instance on
   c, I. carries no second copy of HB or HP, and a later theory-level interpretation I: HP c is
   skipped by the standard (the names under I. are unchanged); definition (in HB) d reaches I.
   exactly once. *)
theory Test5_Restock_H5
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
consts c :: nat
light_locale LF1 = HP
light_locale LF2 = HB c
locale M2 = HB c
locale H5 = LF1 a + LF2 + M2 for a

interpretation I: H5 x for x by unfold_locales simp_all

ML \<open>
val i_facts =
  ["Test5_Restock_H5.I.H5_axioms", "Test5_Restock_H5.I.HB_axioms", "Test5_Restock_H5.I.HP_axioms", "Test5_Restock_H5.I.LF1_axioms",
   "Test5_Restock_H5.I.LF2_axioms", "Test5_Restock_H5.I.M2_axioms", "Test5_Restock_H5.I.hb", "Test5_Restock_H5.I.hp", "Test5_Restock_H5.I.hpl"];
val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H5.I." = i_facts);
val _ = \<^assert> (Thm.prop_of @{thm I.hpl} aconv \<^prop>\<open>c + 0 = c\<close>);
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (exists (fn (_, level, _) => level = Locale.Full) (marks_of ctxt "HP" [\<^term>\<open>c\<close>]));
\<close>

interpretation I: HP c by unfold_locales simp

ML \<open>val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H5.I." = i_facts)\<close>

definition (in HB) d where "d = x"

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Restock_H5.HB.d", "Test5_Restock_H5.I.d"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Restock_H5.I.d" = ["Test5_Restock_H5.I.d_def"]);
\<close>

end
