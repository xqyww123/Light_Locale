(* Plan section 7 test 5 (external use and propagation): the shared-instance diamond.  B is reached
   through the light LF (syntax-only) and through the heavy K (full) in both import orders; the one
   roundup of context H begin starts from empty idents and emits each instance once, so B's instance
   gets one selection value (All) and one Full record, no Syntax_only record.  The levels are read
   in the named contexts (context H begin, and after a theory-level interpretation), and a later
   definition (in B) reaches each registration exactly once, as in the heavy twin.  The three
   theory-level interpretations use distinct instances, so they do not prune each other. *)
theory Test5_Diamond
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale B = fixes b :: nat assumes bl: "b = b"
abbreviation (in B) ba where "ba \<equiv> b + 1"

light_locale LF = B
locale K = B
locale H = LF + K
locale H' = K + LF
locale LFh = B
locale Hh = LFh + K

consts t :: nat  t' :: nat  t'' :: nat

(* the light locale alone: syntax and _axioms present, the heavy theorem absent, syntax-only *)
context LF begin
ML \<open>
val _ = \<^assert> (visible_fact_names \<^context> = ["local.B_axioms", "local.LF_axioms"]);
val _ = \<^assert> (consts_named \<^context> "ba" = ["Test5_Diamond.B.ba", "local.ba"]);
val _ = \<^assert> (marks_of \<^context> "B" [\<^term>\<open>b::nat\<close>] = [([\<^term>\<open>b::nat\<close>], Locale.Syntax_only, ["x"])]);
\<close>
(* the standard interpret in a proof installs the heavy theorem *)
lemma True
proof -
  interpret J: B b by (rule B_axioms)
  ML_prf \<open>val _ = \<^assert> (visible_fact_names \<^context> =
    ["local.B_axioms", "local.J.B_axioms", "local.J.bl", "local.LF_axioms"])\<close>
  show True ..
qed
end

ML \<open>
fun full_only ctxt loc inst = marks_of ctxt loc [inst] = [([inst], Locale.Full, [])];
\<close>

context H begin
ML \<open>
val _ = \<^assert> (visible_fact_names \<^context> =
  ["local.B_axioms", "local.H_axioms", "local.K_axioms", "local.LF_axioms", "local.bl"]);
val _ = \<^assert> (full_only \<^context> "B" \<^term>\<open>b::nat\<close>);
val _ = \<^assert> (full_only \<^context> "LF" \<^term>\<open>b::nat\<close>);
\<close>
end

context H' begin
ML \<open>
val _ = \<^assert> (visible_fact_names \<^context> =
  ["local.B_axioms", "local.H'_axioms", "local.K_axioms", "local.LF_axioms", "local.bl"]);
val _ = \<^assert> (full_only \<^context> "B" \<^term>\<open>b::nat\<close>);
\<close>
end

context Hh begin
ML \<open>
val _ = \<^assert> (visible_fact_names \<^context> =
  ["local.B_axioms", "local.Hh_axioms", "local.K_axioms", "local.LFh_axioms", "local.bl"]);
val _ = \<^assert> (full_only \<^context> "B" \<^term>\<open>b::nat\<close>);
\<close>
end

(* interpret I: LF 7 in a proof: syntax-only under I -- the syntax (I.ba) and the _axioms copies
   present, the heavy theorem absent (plan lines 4092-4093) *)
lemma True
proof -
  interpret I: LF 7 by unfold_locales simp
  ML_prf \<open>
    val _ = \<^assert> (filter (String.isPrefix "local.") (visible_fact_names \<^context>) =
      ["local.I.B_axioms", "local.I.LF_axioms"]);
    val _ = \<^assert> (consts_named \<^context> "ba" = ["Test5_Diamond.B.ba", "local.I.ba"]);
    val _ = \<^assert> (marks_of \<^context> "B" [\<^term>\<open>7::nat\<close>] = [([\<^term>\<open>7::nat\<close>], Locale.Syntax_only, ["I.x"])]);
  \<close>
  show True ..
qed

interpretation I: H t by unfold_locales simp
interpretation I': H' t' by unfold_locales simp
interpretation Ih: Hh t'' by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (facts_under \<^theory> "Test5_Diamond.I." =
  ["Test5_Diamond.I.B_axioms", "Test5_Diamond.I.H_axioms", "Test5_Diamond.I.K_axioms",
   "Test5_Diamond.I.LF_axioms", "Test5_Diamond.I.bl"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Diamond.I'." =
  ["Test5_Diamond.I'.B_axioms", "Test5_Diamond.I'.H'_axioms", "Test5_Diamond.I'.K_axioms",
   "Test5_Diamond.I'.LF_axioms", "Test5_Diamond.I'.bl"]);
val _ = \<^assert> (full_only ctxt "B" \<^term>\<open>t\<close> andalso full_only ctxt "B" \<^term>\<open>t'\<close> andalso full_only ctxt "B" \<^term>\<open>t''\<close>);
val _ = \<^assert> (full_only ctxt "LF" \<^term>\<open>t\<close> andalso full_only ctxt "LF" \<^term>\<open>t'\<close>);
\<close>

definition (in B) d where "d = b"

ML \<open>
val _ = \<^assert> (sort_strings (consts_named (Proof_Context.init_global \<^theory>) "d") =
  ["Test5_Diamond.B.d", "Test5_Diamond.I'.d", "Test5_Diamond.I.d", "Test5_Diamond.Ih.d"]);
val _ = \<^assert> (facts_under \<^theory> "Test5_Diamond.I.d" = ["Test5_Diamond.I.d_def"]);
\<close>

end
