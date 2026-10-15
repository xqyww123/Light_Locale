(* Plan section 7 test 5 (external use and propagation): the heavy twin of row A with + C: M
   (locale LFh = HB c): the same names under I.A., I.B. and I.C.; the fixture is Test5_Mirror_T0. *)
theory Test5_Mirror_AC_Heavy
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

locale LFh = HB c
locale H = A: LFh + B: K + C: M

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_AC_Heavy.I." = ["Test5_Mirror_AC_Heavy.I.A.HB_axioms", "Test5_Mirror_AC_Heavy.I.A.HP_axioms", "Test5_Mirror_AC_Heavy.I.A.LFh_axioms", "Test5_Mirror_AC_Heavy.I.A.hb", "Test5_Mirror_AC_Heavy.I.A.hp", "Test5_Mirror_AC_Heavy.I.A.hpl", "Test5_Mirror_AC_Heavy.I.B.HB_axioms", "Test5_Mirror_AC_Heavy.I.B.HP_axioms", "Test5_Mirror_AC_Heavy.I.B.K_axioms", "Test5_Mirror_AC_Heavy.I.B.hb", "Test5_Mirror_AC_Heavy.I.B.hp", "Test5_Mirror_AC_Heavy.I.B.hpl", "Test5_Mirror_AC_Heavy.I.C.M_axioms", "Test5_Mirror_AC_Heavy.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_AC_Heavy.I.A.hba", "Test5_Mirror_AC_Heavy.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_AC_Heavy.HB.d", "Test5_Mirror_AC_Heavy.I.A.d", "Test5_Mirror_AC_Heavy.I.B.d"]);
\<close>

end
