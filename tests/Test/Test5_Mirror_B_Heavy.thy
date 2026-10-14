(* Plan section 7 test 5 (external use and propagation): the heavy twin of row B with + C: M (locale LFh = HB c): the same names. *)
theory Test5_Mirror_B_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
abbreviation (in HB) hba where "hba \<equiv> x + 1"
consts c :: nat
locale LFh = HB c
locale K = HB
locale M = HB c
locale H = B: K + A: LFh + C: M

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_B_Heavy.I." = ["Test5_Mirror_B_Heavy.I.A.LFh_axioms", "Test5_Mirror_B_Heavy.I.B.HB_axioms", "Test5_Mirror_B_Heavy.I.B.HP_axioms", "Test5_Mirror_B_Heavy.I.B.K_axioms", "Test5_Mirror_B_Heavy.I.B.hb", "Test5_Mirror_B_Heavy.I.B.hp", "Test5_Mirror_B_Heavy.I.B.hpl", "Test5_Mirror_B_Heavy.I.C.M_axioms", "Test5_Mirror_B_Heavy.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_B_Heavy.HB.hba", "Test5_Mirror_B_Heavy.I.B.hba"]);

val _ = \<^assert> (not (can (fn () => Goal.prove ctxt [] [] \<^prop>\<open>HB c\<close> (fn {context, ...} => simp_tac context 1)) ()));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_B_Heavy.HB.d", "Test5_Mirror_B_Heavy.I.B.d"]);
\<close>

end
