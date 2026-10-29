(* Plan section 7 test 6, coverage of the Induct tables and their deletions (plan lines 4700-4706,
   4721-4729): LF.Abs_T_cases -- which the typedef has already registered under T, so each row
   first deletes it -- noted with [cases type: T] in a proof context and declared at theory level
   is keyed on T; fooT2 (no attribute, stored LF ?S ==> Pc ?x ?S ==> Sc ?x, consumes 1, K 1)
   noted with [cases pred: Pc] is registered as the stored theorem and found by find_casesP on
   Pc c S; the deletion sequence declare LF.fooT2[cases pred: Pc] -- positive control in the block
   and the theory -- [cases del] -- gone from the block, and from the theory after end -- and the
   same for [induct pred: Pc] / [induct del]; two [cases pred: Pc] declarations with a different
   consumes in between leave exactly one entry; [cases del] removes LF.Abs_T_cases; the heavy
   twin's block rows (the same batch of Induct-table rows) as controls; the hand-written
   specialised equation from LF.ip.simps[OF
   LF_axioms] is phi-equal to the twin's inductive_simps; proof-local note foo' [case_names a b,
   consumes 1] = LF.foo[OF LF_axioms] equals the twin's block foo up to K (K 0), note r =
   LF.foo[OF LF_axioms] has numbered cases and consumes 0. *)
theory Test6_Coverage
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a  c :: 'a
axiomatization where Sc_ax: "Sc x" and Pc_ax: "Pc x y"

ML \<open>
fun has find ctxt key th = is_some (induct_entry find ctxt key th);
\<close>

context D begin
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
lemma fooT2: "Pc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
inductive_simps ipS: "ip (Suc n)"
ML \<open>val heavy_foo = @{thm foo};\<close>
end
context D begin
declare fooT2[cases pred: Pc]
ML \<open>val _ = \<^assert> (has Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close> @{thm fooT2})\<close>
declare fooT2[cases del]
ML \<open>val _ = \<^assert> (not (has Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close> @{thm fooT2}))\<close>
declare fooT2[induct pred: Pc]
ML \<open>val _ = \<^assert> (has Induct.find_inductP \<^context> \<^prop>\<open>Pc c S\<close> @{thm fooT2})\<close>
declare fooT2[induct del]
ML \<open>val _ = \<^assert> (not (has Induct.find_inductP \<^context> \<^prop>\<open>Pc c S\<close> @{thm fooT2}))\<close>
declare fooT2[cases pred: Pc]
declare fooT2[consumes 0, cases pred: Pc]
ML \<open>val _ = \<^assert> (length (filter (fn r => Thm.eq_thm_prop (r, @{thm fooT2})) (Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close>)) = 1)\<close>
declare fooT2[cases del]
ML \<open>val _ = \<^assert> (has Induct.find_casesT \<^context> \<^typ>\<open>D.T\<close> @{thm Abs_T_cases})\<close>
declare Abs_T_cases [cases del]
ML \<open>val _ = \<^assert> (not (has Induct.find_casesT \<^context> \<^typ>\<open>D.T\<close> @{thm Abs_T_cases}))\<close>
end

context LF begin
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
lemma fooT2: "Pc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end

ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.fooT2} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc x S \<Longrightarrow> Sc x\<close>);
val _ = \<^assert> (Rule_Cases.get_consumes @{thm LF.fooT2} = 1 andalso Setclass.count_of @{thm LF.fooT2} = 1);
\<close>

(* theory level: the typedef's registration deleted first, then LF.Abs_T_cases declared with its
   tag is keyed on T *)
declare LF.Abs_T_cases [cases del]
ML \<open>val _ = \<^assert> (not (has Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases}));\<close>
declare LF.Abs_T_cases [cases type: LF.T]
ML \<open>val _ = \<^assert> (has Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases});\<close>

context LF begin
ML \<open>local
(* proof-context notes: deleted in the local context first *)
val (_, ctxt0) = note_in \<^context> "r0" "[cases del]" @{thm LF.Abs_T_cases};
val _ = \<^assert> (not (has Induct.find_casesT ctxt0 \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases}));
val (r, ctxt) = note_in ctxt0 "r" "[cases type: T]" @{thm LF.Abs_T_cases};
val _ = \<^assert> (has Induct.find_casesT ctxt \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases});
val (r2, ctxt2) = note_in \<^context> "r2" "[cases pred: Pc]" @{thm LF.fooT2};
val SOME e = induct_entry Induct.find_casesP ctxt2 \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2};
val _ = \<^assert> (Thm.eq_thm_prop (e, @{thm LF.fooT2}) andalso Light_Locale_Axiom_Facts.is_light_prop ctxt2 (hd (Thm.prems_of e)));
(* proof-local notes of LF.foo[OF LF_axioms] *)
val (foo', _) = note_in \<^context> "foo'" "[case_names a b, consumes 1]" @{thm LF.foo [OF LF_axioms]};
val _ = \<^assert> (plain_equal (foo', heavy_foo));
val _ = \<^assert> (Rule_Cases.get @{thm LF.foo [OF LF_axioms]} = ([(("1", []), []), (("2", []), [])], 0));
in end\<close>
(* the deletion sequence on the Induct tables *)
declare LF.fooT2[cases pred: Pc]
ML \<open>
val _ = \<^assert> (has Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2});
val _ = \<^assert> (has Induct.find_casesP (thy_ctxt \<^context>) \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2});
\<close>
declare LF.fooT2[cases del]
ML \<open>val _ = \<^assert> (not (has Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2}))\<close>
declare LF.fooT2[induct pred: Pc]
ML \<open>
val _ = \<^assert> (has Induct.find_inductP \<^context> \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2});
val _ = \<^assert> (has Induct.find_inductP (thy_ctxt \<^context>) \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2});
\<close>
declare LF.fooT2[induct del]
ML \<open>val _ = \<^assert> (not (has Induct.find_inductP \<^context> \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2}))\<close>
(* two declarations, a different consumes in between: exactly one entry *)
declare LF.fooT2[cases pred: Pc]
declare LF.fooT2[consumes 0, cases pred: Pc]
ML \<open>
val _ = \<^assert> (length (filter (fn r => Thm.eq_thm_prop (r, @{thm LF.fooT2})) (Induct.find_casesP \<^context> \<^prop>\<open>Pc c S\<close>)) = 1);
\<close>
declare LF.fooT2[cases del]
(* [cases del] on the package's own rule (registered again at theory level above) *)
ML \<open>val _ = \<^assert> (has Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases})\<close>
declare LF.Abs_T_cases [cases del]
ML \<open>val _ = \<^assert> (not (has Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases}))\<close>
(* the hand-written specialised equation *)
lemma ipS': "LF.ip S (Suc n) = (Pc S n \<and> LF.ip S n)" by (simp add: LF.ip.simps[OF LF_axioms, of "Suc n"])
end

ML \<open>
val tctxt = \<^context>;
val _ = \<^assert> (not (has Induct.find_casesP tctxt \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2}));
val _ = \<^assert> (not (has Induct.find_inductP tctxt \<^prop>\<open>Pc c S\<close> @{thm LF.fooT2}));
val _ = \<^assert> (not (has Induct.find_casesT tctxt \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases}));
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm LF.ipS'}, @{thm D.ipS}));
\<close>

end
