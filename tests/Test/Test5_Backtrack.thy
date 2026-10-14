(* Plan section 7 test 5 (external use and propagation): prefix backtracking (a known consequence of decision 6): interpretation I: LF t, then interpretation Zp: HB t on the same key; a later abbreviation (in HB) appears under Zp. and not under I. *)
theory Test5_Backtrack
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
consts t :: nat
light_locale LF = HB
interpretation I: LF t by unfold_locales simp
interpretation Zp: HB t by unfold_locales simp
abbreviation (in HB) nabb where "nabb \<equiv> x + 1"

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (consts_named ctxt "nabb" = ["Test5_Backtrack.HB.nabb", "Test5_Backtrack.Zp.nabb"]);
val _ = \<^assert> (marks_of ctxt "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Backtrack.I." = ["Test5_Backtrack.I.HB_axioms", "Test5_Backtrack.I.LF_axioms"]);
\<close>

end
