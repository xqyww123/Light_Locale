(* Plan section 7 test 5 (external use and propagation): the heavy twin of row B (locale LFh = HB c,
   heavy first, no third arrival; plan line 4174 "heavy 孪生 locale LF' = HB c 同序逐项相同"): the
   same names as the light row B -- the special instance under A is pruned by the general one
   under B; the fixture is Test5_Mirror_T0.  The + C: M variant is Test5_Mirror_BC_Heavy. *)
theory Test5_Mirror_B_Heavy
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

locale LFh = HB c
locale H = B: K + A: LFh

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_B_Heavy.I." = ["Test5_Mirror_B_Heavy.I.A.LFh_axioms", "Test5_Mirror_B_Heavy.I.B.HB_axioms", "Test5_Mirror_B_Heavy.I.B.HP_axioms", "Test5_Mirror_B_Heavy.I.B.K_axioms", "Test5_Mirror_B_Heavy.I.B.hb", "Test5_Mirror_B_Heavy.I.B.hp", "Test5_Mirror_B_Heavy.I.B.hpl", "Test5_Mirror_B_Heavy.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_B_Heavy.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_B_Heavy.HB.d", "Test5_Mirror_B_Heavy.I.B.d"]);
\<close>

end
