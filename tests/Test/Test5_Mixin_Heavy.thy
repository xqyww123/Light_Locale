(* Plan section 7 test 5 (external use and propagation), the inherited registration mixin that
   rewrites the key instance matched by inclusion against a Syntax_only mark (Heavy side): after
   interpretation I: HP c rewrites "k = e", interpretation J: LF y for y and interpretation J: HB c k,
   definition (in HB) d succeeds with exactly one J.d and no Duplicate constant declaration.  The
   qualified variant LF a + B: K succeeds as a control. *)
theory Test5_Mixin_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts c :: nat  k :: nat
definition e :: nat where "e = k"
locale HP = fixes y :: nat assumes "y = y"
locale HB = HP x for x + fixes z :: nat
lemma (in HB) hz: "z + x = x + z" by simp
locale LF = HB a k for a

interpretation I: HP c rewrites "k = e" by unfold_locales (simp_all add: e_def)
interpretation J: LF y for y by unfold_locales simp_all
interpretation J: HB c k by unfold_locales simp_all

definition (in HB) d where "d = z"

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (consts_named ctxt "d" = ["Test5_Mixin_Heavy.HB.d", "Test5_Mixin_Heavy.J.d"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Mixin_Heavy.J." =
  ["Test5_Mixin_Heavy.J.HB_axioms", "Test5_Mixin_Heavy.J.HP_axioms", "Test5_Mixin_Heavy.J.LF_axioms", "Test5_Mixin_Heavy.J.d_def", "Test5_Mixin_Heavy.J.hz"]);
(*the second J command is skipped by the standard (locale.ML:624), so J.hz is the general instance*)
val _ = \<^assert> (Thm.prop_of @{thm J.hz} aconv Logic.varify_global \<^prop>\<open>k + (y::nat) = y + k\<close>);
\<close>

locale K = HB c k
locale HQ = LF a + B: K for a
interpretation Q: HQ y for y by unfold_locales simp_all

ML \<open>val _ = \<^assert> (facts_under \<^theory> "Test5_Mixin_Heavy.Q." = ["Test5_Mixin_Heavy.Q.B.K_axioms", "Test5_Mixin_Heavy.Q.HQ_axioms"])\<close>

end
