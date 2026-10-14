(* Plan section 7 test 4 (upgrade), theory-level group (a): two commands, same named effect,
   selection Rest.  interpretation I: LF x for x reaches HB ?x syntax-only under I; interpretation
   I: HB t then upgrades it -- no Duplicate fact declaration, exactly one I.HB_axioms that still
   carries [simp, intro!], the heavy theorems present.  The names installed by the two commands are
   disjoint, and their union without I.LF_axioms is what the control interpretation of HB t installs
   in a theory that has never seen LF (Test4_Control, the literal hb_installed). *)
theory Test4_A
  imports Test4_Fixture
begin

light_locale LF = HB

interpretation I: LF x for x by unfold_locales simp

ML \<open>val after2 = Test_Support.facts_under \<^theory> "Test4_A.I."\<close>

interpretation I: HB t by unfold_locales simp

ML \<open>
val after3 = Test_Support.facts_under \<^theory> "Test4_A.I.";
val added = subtract (op =) after2 after3;
val _ = \<^assert> (after2 = ["Test4_A.I.HB_axioms", "Test4_A.I.LF_axioms"]);
val _ = \<^assert> (added = ["Test4_A.I.hb", "Test4_A.I.hb2"]);
val _ = \<^assert> (null (inter (op =) after2 added));
val _ = \<^assert>
  (map (unprefix "Test4_A.I.") (remove (op =) "Test4_A.I.LF_axioms" (after2 @ added)) = hb_installed);
\<close>

(* I.HB_axioms still carries [simp]: simp closes HB t *)
lemma "HB t" by simp

end
