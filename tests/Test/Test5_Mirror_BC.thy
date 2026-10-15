(* Plan section 7 test 5 (external use and propagation): the mirror pair, row B with + C: M: I.A.
   stays empty; the fixture is Test5_Mirror_T0. *)
theory Test5_Mirror_BC
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

light_locale LF = HB c
locale H = B: K + A: LF + C: M

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_BC.I." = ["Test5_Mirror_BC.I.A.LF_axioms", "Test5_Mirror_BC.I.B.HB_axioms", "Test5_Mirror_BC.I.B.HP_axioms", "Test5_Mirror_BC.I.B.K_axioms", "Test5_Mirror_BC.I.B.hb", "Test5_Mirror_BC.I.B.hp", "Test5_Mirror_BC.I.B.hpl", "Test5_Mirror_BC.I.C.M_axioms", "Test5_Mirror_BC.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_BC.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
(*HB c is never emitted: the only record is the general one*)
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>c\<close>] = [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, [])]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_BC.HB.d", "Test5_Mirror_BC.I.B.d"]);
\<close>

end
