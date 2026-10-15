(* Plan section 7 test 5 (external use and propagation): the mirror pair, row A (light first); the
   fixture is Test5_Mirror_T0.  Under I.A. HB's Plain theorems are absent, its syntax and exactly
   one I.A.HB_axioms [simp, intro!] present (simp closes HB c); under I.B. the theorems are present.
   A later definition (in HB) d reaches both I.A.d and I.B.d; notation (in HB) succeeds (plan line
   4099: a locale constant's notation reaches no theory-level registration, in stock as well). *)
theory Test5_Mirror_A
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

light_locale LF = HB c
locale H = A: LF + B: K

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_A.I." = ["Test5_Mirror_A.I.A.HB_axioms", "Test5_Mirror_A.I.A.HP_axioms", "Test5_Mirror_A.I.A.LF_axioms", "Test5_Mirror_A.I.B.HB_axioms", "Test5_Mirror_A.I.B.HP_axioms", "Test5_Mirror_A.I.B.K_axioms", "Test5_Mirror_A.I.B.hb", "Test5_Mirror_A.I.B.hp", "Test5_Mirror_A.I.B.hpl", "Test5_Mirror_A.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_A.I.A.hba", "Test5_Mirror_A.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
val _ = \<^assert> (marks_are ctxt "HB" [\<^term>\<open>c\<close>] [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Syntax_only, ["I.A.x"])]);
val _ = \<^assert> (by_simp ctxt \<^prop>\<open>HB c\<close>);
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_A.HB.d", "Test5_Mirror_A.I.A.d", "Test5_Mirror_A.I.B.d"]);
\<close>

end
