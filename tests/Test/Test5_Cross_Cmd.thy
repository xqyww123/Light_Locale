(* Plan section 7 test 5 (external use and propagation): the cross-command form of H7: theory-level interpretation I: LF x for x, interpretation I: K, then interpretation I: HB x for x fails loudly on the light side. *)
theory Test5_Cross_Cmd
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts c :: nat  t :: nat  t1 :: nat  t2 :: nat
light_locale LF = HB
locale K = HB c
interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all

ML \<open>
val _ = fails_prefix "Duplicate fact declaration" (fn () => interpretation_cmd "I: HB x for x" \<^theory>);
\<close>

end
