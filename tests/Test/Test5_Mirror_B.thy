(* Plan section 7 test 5 (external use and propagation): the mirror pair, row B (heavy first); the
   fixture is Test5_Mirror_T0.  HB ?x arrives through K first and records Full_mark; the light
   edge's request for HB c is redundant and is never emitted: under I.A. HB's syntax, _axioms and
   Plain theorems are all absent (only I.A.LF_axioms), under I.B. everything is present with
   exactly one I.B.HB_axioms without [simp, intro!] (simp does not close HB c). *)
theory Test5_Mirror_B
  imports Test5_Mirror_T0
begin

ML \<open>open Test_Support\<close>

light_locale LF = HB c
locale H = B: K + A: LF

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_B.I." = ["Test5_Mirror_B.I.A.LF_axioms", "Test5_Mirror_B.I.B.HB_axioms", "Test5_Mirror_B.I.B.HP_axioms", "Test5_Mirror_B.I.B.K_axioms", "Test5_Mirror_B.I.B.hb", "Test5_Mirror_B.I.B.hp", "Test5_Mirror_B.I.B.hpl", "Test5_Mirror_B.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_B.I.B.hba", "Test5_Mirror_T0.HB.hba"]);
(*HB c is never emitted: the only record is the general one*)
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>c\<close>] = [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, [])]);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>HB c\<close>));
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_B.HB.d", "Test5_Mirror_B.I.B.d"]);
\<close>

end
