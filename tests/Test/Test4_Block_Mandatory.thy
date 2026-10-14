(* Plan section 7 test 4 (upgrade), the block rows with the mandatory bit: the edge HB < q?: HQ
   records the effect under the optional qualifier q, the proof inside context LF begin interprets
   the same instance under the mandatory q: -- same named effect, so the abbreviation q.hqa is not
   declared again (selection Rest) and only the Plain note q.hq is added.  The sublocale edge is
   persistent theory state, so this leaf owns it. *)
theory Test4_Block_Mandatory
  imports Test4_Fixture
begin

sublocale HB < q?: HQ "Suc x" by unfold_locales simp

light_locale LF = HB

locale D = HB

ML \<open>
fun under prefix = filter (String.isPrefix prefix);
val d_facts = Test_Support.visible_fact_names (Locale.init (Locale.check_global \<^theory> ("D", Position.none)) \<^theory>);
val _ = \<^assert> (d_facts =
  ["local.D_axioms", "local.HB_axioms", "local.hb", "local.hb2", "local.q.HQ_axioms", "local.q.hq"]);
\<close>

context LF begin

ML_val \<open>
val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.q.hqa"]);
val _ = \<^assert> (Test_Support.visible_fact_names \<^context> = ["local.HB_axioms", "local.LF_axioms", "local.q.HQ_axioms"]);
\<close>

lemma True
proof -
  interpret q: HQ "Suc x" by (rule q.HQ_axioms)
  ML_val \<open>
    (*no Duplicate constant declaration, exactly one q.hqa; the names under q. now equal the
      heavy twin's; the only addition is the Plain note q.hq*)
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.q.hqa"]);
    val _ = \<^assert> (Test_Support.visible_fact_names \<^context> =
      ["local.HB_axioms", "local.LF_axioms", "local.q.HQ_axioms", "local.q.hq"]);
    val _ = \<^assert> (under "local.q." (Test_Support.visible_fact_names \<^context>) = under "local.q." d_facts);
  \<close>
  (* after the upgrade, interpreting the same instance again is skipped by the standard *)
  interpret q: HQ "Suc x" by (rule q.HQ_axioms)
  ML_val \<open>
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.q.hqa"]);
    val _ = \<^assert> (Test_Support.visible_fact_names \<^context> =
      ["local.HB_axioms", "local.LF_axioms", "local.q.HQ_axioms", "local.q.hq"]);
  \<close>
  show True ..
qed

(* positive control: a new named effect r declares r.hqa (selection All) *)
lemma True
proof -
  interpret r: HQ "Suc x" by (rule q.HQ_axioms)
  ML_val \<open>
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.q.hqa", "local.r.hqa"]);
    val _ = \<^assert> (Test_Support.visible_fact_names \<^context> =
      ["local.HB_axioms", "local.LF_axioms", "local.q.HQ_axioms", "local.r.HQ_axioms", "local.r.hq"]);
  \<close>
  show True ..
qed

(* the HQ instantiation of the one-goal row (plan section 11 (12)): HQ has no defines, so
   unfold_locales closes the obligation with no goal left -- the syntax-only copy of q.HQ_axioms
   carries witness_add (plan section 3.1, the _axioms note is replayed on every activation) *)
lemma True
proof -
  interpret HQ "Suc x" proof unfold_locales qed
  ML_val \<open>
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.hqa", "local.q.hqa"]);
  \<close>
  show True ..
qed

end

(* the contrast: a context that never activated the instance, where unfold_locales leaves exactly
   one goal, HQ's assumption -- this guards against the syntax-only copy's witness leaking into the
   theory context *)
lemma True
proof -
  interpret HQ "Suc t"
  proof unfold_locales
    show "Suc t = Suc t" ..
  qed
  ML_val \<open>
    val _ = \<^assert> (Test_Support.consts_named \<^context> "hqa" = ["Test4_Fixture.HQ.hqa", "local.hqa"]);
    val _ = \<^assert> (under "local." (Test_Support.visible_fact_names \<^context>) = ["local.HQ_axioms", "local.hq"]);
  \<close>
  show True ..
qed

end
