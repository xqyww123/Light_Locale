(* Plan section 7 test 5 (external use and propagation): the heavy twin of the cross-command form: the third command succeeds with exactly one I.hb. *)
theory Test5_Cross_Cmd_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  t :: nat  t1 :: nat  t2 :: nat
locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all
interpretation I: HB x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_Cmd_Heavy.I." =
  ["Test5_Cross_Cmd_Heavy.I.HB_axioms", "Test5_Cross_Cmd_Heavy.I.K_axioms",
   "Test5_Cross_Cmd_Heavy.I.LF_axioms", "Test5_Cross_Cmd_Heavy.I.hb"]);
\<close>

end
