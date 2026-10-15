(* The heavy twin of Test5_Filtered (plan lines 4128-4129): the same five commands succeed on
   locale LF = HB x c for x.  Step 1 (I: LF x for x) registers HB [?x, c] Full and installs I.hb;
   step 2 (I: K) is pruned; step 3 (J: HB x z for x z) registers [?x, ?z] Full; step 4 (Q: K4 x for x)
   is filtered by the [?x, ?z] record; step 5 (definition (in HB) dd) gives exactly I.dd and J.dd. *)
theory Test5_Filtered_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x z :: nat assumes hbx: "x = x"
lemma (in HB) hb: "x + z = z + x" by simp
consts c :: nat  d :: nat
locale LF = HB x c for x
locale K = HB d c
locale K4 = HB x c for x

interpretation I: LF x for x by unfold_locales simp_all
interpretation I: K by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered_Heavy.I." =
  ["Test5_Filtered_Heavy.I.HB_axioms", "Test5_Filtered_Heavy.I.K_axioms", "Test5_Filtered_Heavy.I.LF_axioms", "Test5_Filtered_Heavy.I.hb", "Test5_Filtered_Heavy.I.hbx"]);
\<close>

interpretation J: HB x z for x z by unfold_locales simp_all
interpretation Q: K4 x for x by unfold_locales simp_all

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered_Heavy.Q." = ["Test5_Filtered_Heavy.Q.K4_axioms"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Filtered_Heavy.J." = ["Test5_Filtered_Heavy.J.HB_axioms", "Test5_Filtered_Heavy.J.hb", "Test5_Filtered_Heavy.J.hbx"]);
\<close>

definition (in HB) dd where "dd = x"

ML \<open>
val _ = \<^assert> (sort_strings (consts_named (Proof_Context.init_global \<^theory>) "dd") =
  ["Test5_Filtered_Heavy.HB.dd", "Test5_Filtered_Heavy.I.dd", "Test5_Filtered_Heavy.J.dd"]);
\<close>

end
