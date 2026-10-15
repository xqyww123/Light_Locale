(* Plan section 7 test 5 (external use and propagation), the cross-command same prefix: after
   interpretation P: LF t the record of HB t is Syntax_only with effect P; interpretation P: HB t
   upgrades it to exactly one Full record; a later abbreviation and definition (in HB) each reach
   P. exactly once; notation (in HB) succeeds and prints the same for P. and the heavy control
   Ph: HB t' (plan line 4099, relaxed: notation reaches no theory-level registration). *)
theory Test5_Cross_Prefix
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale HB = fixes x :: nat assumes hb: "x = x"
light_locale LF = HB
consts t :: nat  t' :: nat

interpretation P: LF t by unfold_locales simp

ML \<open>
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] =
  [([\<^term>\<open>t\<close>], Locale.Syntax_only, ["P.x"])]);
\<close>

interpretation P: HB t by unfold_locales simp

interpretation Ph: HB t' by unfold_locales simp

ML \<open>
val _ = \<^assert> (marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] =
  [([\<^term>\<open>t\<close>], Locale.Full, [])]);
\<close>

abbreviation (in HB) hba where "hba \<equiv> x + 1"
definition (in HB) hbd where "hbd = x + 2"
notation (in HB) hbd ("HBD")

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (sort_strings (consts_named ctxt "hba") = ["Test5_Cross_Prefix.HB.hba", "Test5_Cross_Prefix.P.hba", "Test5_Cross_Prefix.Ph.hba"]);
val _ = \<^assert> (sort_strings (consts_named ctxt "hbd") = ["Test5_Cross_Prefix.HB.hbd", "Test5_Cross_Prefix.P.hbd", "Test5_Cross_Prefix.Ph.hbd"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Cross_Prefix.P." =
  ["Test5_Cross_Prefix.P.HB_axioms", "Test5_Cross_Prefix.P.LF_axioms", "Test5_Cross_Prefix.P.hb",
   "Test5_Cross_Prefix.P.hbd_def"]);
(*the notation prints the same for P. and the heavy control*)
val shown = apply2 (XML.content_of o YXML.parse_body o Syntax.string_of_term ctxt) (\<^term>\<open>P.hbd\<close>, \<^term>\<open>Ph.hbd\<close>);
val _ = \<^assert> (shown = ("HBD", "HBD") orelse shown = ("P.hbd", "Ph.hbd"));
\<close>

end
