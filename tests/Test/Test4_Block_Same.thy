(* Plan section 7 test 4 (upgrade), the block row with the same named effect: the edge HB < HQ
   without a qualifier, the proof inside context LF begin interprets the same instance without a
   qualifier -- hqa is not declared again, only the Plain note hq is added. *)
theory Test4_Block_Same
  imports Test4_Fixture
begin

sublocale HB < HQ "Suc x" by unfold_locales simp

light_locale LF = HB

context LF begin

ML \<open>
val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.hqa"]);
val _ = \<^assert> (Test_Support.visible_fact_names \<^context> = ["local.HB_axioms", "local.HQ_axioms", "local.LF_axioms"]);
\<close>

lemma True
proof -
  interpret HQ "Suc x" by (rule HQ_axioms)
  ML_prf \<open>
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.hqa"]);
    val _ = \<^assert> (Test_Support.visible_fact_names \<^context> =
      ["local.HB_axioms", "local.HQ_axioms", "local.LF_axioms", "local.hq"]);
  \<close>
  show True ..
qed

end

end
