(* Plan section 7 test 5 (external use and propagation): the mirror pair, row A (light first).  Under I.A. HB's Plain theorems are absent, its syntax and exactly one I.A.HB_axioms [simp, intro!] present (simp closes HB c); under I.B. the theorems are present.  A later definition (in HB) d reaches both I.A.d and I.B.d; notation (in HB) has the same shape. *)
theory Test5_Mirror_A
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
abbreviation (in HB) hba where "hba \<equiv> x + 1"
consts c :: nat
light_locale LF = HB c
locale K = HB
locale M = HB c
locale H = A: LF + B: K

interpretation I: H x for x by unfold_locales simp_all

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Mirror_A.I." = ["Test5_Mirror_A.I.A.HB_axioms", "Test5_Mirror_A.I.A.HP_axioms", "Test5_Mirror_A.I.A.LF_axioms", "Test5_Mirror_A.I.B.HB_axioms", "Test5_Mirror_A.I.B.HP_axioms", "Test5_Mirror_A.I.B.K_axioms", "Test5_Mirror_A.I.B.hb", "Test5_Mirror_A.I.B.hp", "Test5_Mirror_A.I.B.hpl", "Test5_Mirror_A.I.H_axioms"]);
val _ = \<^assert> (consts_named ctxt "hba" = ["Test5_Mirror_A.HB.hba", "Test5_Mirror_A.I.A.hba", "Test5_Mirror_A.I.B.hba"]);
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>c\<close>] = [([Var (("x", 0), \<^typ>\<open>nat\<close>)], Locale.Full, []), ([\<^term>\<open>c\<close>], Locale.Syntax_only, ["I.A.x"])]);
val _ = \<^assert> (can (fn () => Goal.prove ctxt [] [] \<^prop>\<open>HB c\<close> (fn {context, ...} => simp_tac context 1)) ());
\<close>

definition (in HB) d where "d = x"
notation (in HB) d ("DD")

ML \<open>
val _ = \<^assert> (consts_named (Proof_Context.init_global \<^theory>) "d" = ["Test5_Mirror_A.HB.d", "Test5_Mirror_A.I.A.d", "Test5_Mirror_A.I.B.d"]);
\<close>

end
