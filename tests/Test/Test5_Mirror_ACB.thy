(* Plan section 7 test 5 (external use and propagation): the mirror pair, the third import order
   A: LF + C: M + B: K behaves per instance like row A with + C: M (levels do not depend on the
   import order); the fixture is Test5_Mirror_T0. *)
theory Test5_Mirror_ACB
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

light_locale LF = HB c
locale H = A: LF + C: M + B: K

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_ACB.I." = ["Test5_Mirror_ACB.I.A.HB_axioms", "Test5_Mirror_ACB.I.A.HP_axioms", "Test5_Mirror_ACB.I.A.LF_axioms", "Test5_Mirror_ACB.I.A.hb", "Test5_Mirror_ACB.I.A.hp", "Test5_Mirror_ACB.I.A.hpl", "Test5_Mirror_ACB.I.B.HB_axioms", "Test5_Mirror_ACB.I.B.HP_axioms", "Test5_Mirror_ACB.I.B.K_axioms", "Test5_Mirror_ACB.I.B.hb", "Test5_Mirror_ACB.I.B.hp", "Test5_Mirror_ACB.I.B.hpl", "Test5_Mirror_ACB.I.C.M_axioms", "Test5_Mirror_ACB.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_ACB.I.A.hba", "Test5_Mirror_ACB.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
val _ = \<^assert> (marks_are ctxt "HB" [\<^term>\<open>c\<close>] [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Full, [])]);
val _ = \<^assert> (marks_are ctxt "HP" [\<^term>\<open>c\<close>] [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Full, [])]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_ACB.HB.d", "Test5_Mirror_ACB.I.A.d", "Test5_Mirror_ACB.I.B.d"]);
\<close>

end
