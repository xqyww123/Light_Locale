(* Plan section 7 test 5 (external use and propagation): the mirror pair, row A with the third
   arrival C: M; the fixture is Test5_Mirror_T0.  HB's theorems and HP's hpl are reachable under
   I.A. (the first-arrival prefix: the upgrade re-descends with the first morphism) and I.C. holds
   no HB or HP material; the full activation of HB c carries the heavy _axioms without
   [simp, intro!] (decision 11), so simp does not close HB c here. *)
theory Test5_Mirror_AC
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

light_locale LF = HB c
locale H = A: LF + B: K + C: M

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_AC.I." = ["Test5_Mirror_AC.I.A.HB_axioms", "Test5_Mirror_AC.I.A.HP_axioms", "Test5_Mirror_AC.I.A.LF_axioms", "Test5_Mirror_AC.I.A.hb", "Test5_Mirror_AC.I.A.hp", "Test5_Mirror_AC.I.A.hpl", "Test5_Mirror_AC.I.B.HB_axioms", "Test5_Mirror_AC.I.B.HP_axioms", "Test5_Mirror_AC.I.B.K_axioms", "Test5_Mirror_AC.I.B.hb", "Test5_Mirror_AC.I.B.hp", "Test5_Mirror_AC.I.B.hpl", "Test5_Mirror_AC.I.C.M_axioms", "Test5_Mirror_AC.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_AC.I.A.hba", "Test5_Mirror_AC.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
val _ = \<^assert> (marks_are ctxt "HB" [\<^term>\<open>c\<close>] [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Full, [])]);
val _ = \<^assert> (marks_are ctxt "HP" [\<^term>\<open>c\<close>] [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Full, [])]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_AC.HB.d", "Test5_Mirror_AC.I.A.d", "Test5_Mirror_AC.I.B.d"]);
\<close>

end
