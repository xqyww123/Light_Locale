(* Plan section 7 test 4 (upgrade), theory-level group (b): the ground command first, then the
   general instance, then the upgrade of the ground one -- Pattern.matchess takes the recorded
   instance as the pattern, so the recorded [t] must not swallow [?x] and the upgrade of [t] under
   J must find its own record.  Same assertions as group (a). *)
theory Test4_B
  imports Test4_Fixture
begin

light_locale LF = HB

interpretation J: LF t by unfold_locales simp

interpretation I: LF x for x by unfold_locales simp

ML \<open>
val after2 = Test_Support.facts_under \<^theory> "Test4_B.";
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_B.J." = ["Test4_B.J.HB_axioms", "Test4_B.J.LF_axioms"]);
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test4_B.I." = ["Test4_B.I.HB_axioms", "Test4_B.I.LF_axioms"]);
\<close>

interpretation J: HB t by unfold_locales simp

ML \<open>
val added = subtract (op =) after2 (Test_Support.facts_under \<^theory> "Test4_B.");
val _ = \<^assert> (added = ["Test4_B.J.hb", "Test4_B.J.hb2"]);
val j2 = filter (String.isPrefix "Test4_B.J.") after2;
val _ = \<^assert>
  (map (unprefix "Test4_B.J.") (remove (op =) "Test4_B.J.LF_axioms" (j2 @ added)) = hb_installed);
\<close>

(* J.HB_axioms still carries [simp] (plan 4077): the general I.HB_axioms (HB ?x) would close the
   goal by itself, so it is taken out; Test4_D is the negative control *)
lemma "HB t" by (simp del: I.HB_axioms)

end
