(* Plan section 7 test 6, the Exported_Premises unit rows (plan lines 4576-4600, 4604-4610,
   4615-4625, 4629-4645): count_of, get_consumes and the K-offset consumes/default_consumes on
   untagged and tagged theorems, which attributes keep the tag, put, tag-string sharing, discharge,
   put_major_prem_first, own_major_prem, kind_make_elim, [dest] on a rule without own premises
   (fails in the block, accepted on the theory copy and read back as LF ?S ==> ...), the n = K
   usage outside the block, [exported_premises n] in all its forms including the out-of-range
   error, and the in-block writings foo0 / x1 / e1. *)
theory Test6_Exported
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun attr att th ctxt = #1 (Thm.apply_attribute att th (Context.Proof ctxt));
\<close>

consts Rc :: 'a  Sc :: 'a  Pc :: 'a  Qc :: 'a  c :: 'a
axiomatization where Sc_ax: "Sc x" and Pc_ax: "Pc x y" and Pc1_ax: "Pc x" and Qc1_ax: "Qc x"

lemma untagged: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma tagged_c [consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)

context D begin
lemma fooQ: "Qc x \<Longrightarrow> Pc x y" by (rule Pc_ax)
lemma z0: "Sc x" by (rule Sc_ax)
lemma zP: "Pc S" by (rule Pc1_ax)
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML_val \<open>\<^assert> (not (can (fn () => theorem_in \<^context> (Binding.name "z") "[dest]" "Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax})) ()))\<close>
ML \<open>
val heavy_r = #1 (note_in \<^context> "r" "[cases pred: Qc]" @{thm fooQ [of c]});
\<close>
end

context LF begin
lemma fooP: "Pc x y" by (rule Pc_ax)
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma fooQ: "Qc x \<Longrightarrow> Pc x y" by (rule Pc_ax)
lemma bad: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma z0: "Sc x" by (rule Sc_ax)
lemma zP: "Pc S" by (rule Pc1_ax)
lemma foo_iff: "A \<longleftrightarrow> A" by (rule refl)
lemma fooB: "(\<And>a b. Q a b) \<Longrightarrow> Q c c" by (drule_tac x = c in meta_spec, drule_tac x = c in meta_spec, assumption)
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
ML_val \<open>\<^assert> (not (can (fn () => theorem_in \<^context> (Binding.name "z") "[dest]" "Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax})) ()))\<close>
(* e1 [exported_premises 3] on a one-premise block form: out of range; [exported_premises 2] on
   two premises: accepted, stored with K 1 *)
ML_val \<open>
fun insert_assume ctxt i = Method.insert_tac ctxt @{thms LF_axioms} i THEN assume_tac ctxt i;
val _ = \<^assert> ((theorem_in \<^context> (Binding.name "e1") "[exported_premises 3]" "A \<Longrightarrow> A" insert_assume; false)
  handle ERROR msg => String.isPrefix "exported_premises: count out of range" (Protocol_Message.clean_output msg));
\<close>
lemma e1 [exported_premises 2]: "A \<Longrightarrow> A \<Longrightarrow> A"
  apply (insert LF_axioms) apply assumption done
(* the same-row note with cases pred, up to K with the twin's *)
ML_val \<open>
val r = #1 (note_in \<^context> "r" "[cases pred: Qc]" @{thm LF.fooQ [of _ c]});
val _ = \<^assert> (diff_K 1 (r, heavy_r));
(* the notes in a proof in the block (plan lines 4629-4632), driven through note_in -- the
   Proof_Context.note_thmss an in-proof note runs, the attributes parsed from their text: THEN
   clears the tag, [exported_premises 1] writes it back *)
val (r, ctxt_r) = note_in \<^context> "r" "[THEN conjunct1]" @{thm LF.foo};
val _ = \<^assert> (Exported_Premises.count_of r = 0);
val (r', _) = note_in ctxt_r "r'" "[exported_premises 1]" r;
val _ = \<^assert> (Exported_Premises.count_of r' = 1 andalso not (AList.defined (op =) (Thm.get_tags r') "consumes")
  andalso Rule_Cases.get_consumes r' = 1 andalso Exported_Premises.strong_consumes r' = 0);
(* THEN renames to conjunct1's ?P ?Q: compared up to variable names *)
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind r'),
  Logic.varify_global \<^prop>\<open>A \<Longrightarrow> LF S \<Longrightarrow> B \<Longrightarrow> (A \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
\<close>
end

ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.e1} = 1 andalso
  Thm.prop_of @{thm LF.e1} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A\<close>);
val ctxt = \<^context>;
val fooP = @{thm LF.fooP} and foo = @{thm LF.foo};
(* count_of, get_consumes *)
val _ = \<^assert> (Exported_Premises.count_of @{thm untagged} = 0);
val _ = \<^assert> (Exported_Premises.count_of fooP = 1 andalso Rule_Cases.get_consumes fooP = 1
  andalso not (AList.defined (op =) (Thm.get_tags fooP) "consumes"));
val rot = @{thm LF.bad [rotated]};
val _ = \<^assert> (Exported_Premises.count_of rot = 0 andalso Rule_Cases.get_consumes rot = 0);
(* consumes / default_consumes on untagged theorems, as stock: the theorem with the consumes tag
   in front of its tags (rule_cases.ML:221-224, more_thm.ML:623; the result on the stock copy
   written by hand, section 11 item (22)) *)
val _ = List.app (fn u =>
    \<^assert> (Thm.eq_thm (u, @{thm untagged}) andalso Thm.get_tags u = ("consumes", "1") :: Thm.get_tags @{thm untagged}))
  [attr (Rule_Cases.consumes 1) @{thm untagged} ctxt, attr (Rule_Cases.consumes (~1)) @{thm untagged} ctxt,
   Rule_Cases.default_consumes 1 @{thm untagged}];
val _ = \<^assert> (Thm.eq_thm_strict (Rule_Cases.default_consumes 1 @{thm tagged_c}, @{thm tagged_c}));
(* on tagged theorems: offset by K *)
val f1 = attr (Rule_Cases.consumes 1) foo ctxt;
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags f1) "consumes" = SOME "2" andalso Exported_Premises.count_of f1 = 1);
val f2 = attr (Rule_Cases.consumes (~1)) foo ctxt;
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags f2) "consumes" = SOME "2");
val p1 = Rule_Cases.default_consumes 1 fooP;
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags p1) "consumes" = SOME "2");
val _ = \<^assert> (Thm.eq_thm_strict (Rule_Cases.default_consumes 1 foo, foo));
(* get_consumes: the max of K and the recorded value *)
val _ = \<^assert> (Rule_Cases.get_consumes fooP = 1);
val _ = \<^assert> (Rule_Cases.get_consumes @{thm LF.fooP [exported_premises 0]} = 0);
val p0 = Rule_Cases.put_consumes (SOME 0) fooP;
val _ = \<^assert> (Rule_Cases.get_consumes p0 = 1 andalso Exported_Premises.strong_consumes p0 = 0);
(* which attributes keep the tag *)
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooP [of _ c]} = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooP [where x = c]} = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooB [params a b]} = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.foo [THEN conjunct1]} = 0 andalso null (Thm.get_tags @{thm LF.foo [THEN conjunct1]}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.foo [rotated]} = 0 andalso null (Thm.get_tags @{thm LF.foo [rotated]}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooP [simplified]} = 1);
(* put *)
val _ = \<^assert> (Thm.eq_thm_strict (Exported_Premises.put 0 @{thm untagged}, @{thm untagged}));
val fp0 = Exported_Premises.put 0 foo;
val _ = \<^assert> (not (has_K_tag fp0) andalso AList.lookup (op =) (Thm.get_tags fp0) "consumes" = SOME "2"
  andalso tags_without_K foo = Thm.get_tags fp0);
val up1 = Exported_Premises.put 1 @{thm untagged};
val _ = \<^assert> (Exported_Premises.count_of up1 = 1 andalso not (AList.defined (op =) (Thm.get_tags up1) "consumes"));
(* the tag strings of two freshly stored theorems are shared *)
val _ = \<^assert> (pointer_eq (the (AList.lookup (op =) (Thm.get_tags fooP) "exported_premises"),
  the (AList.lookup (op =) (Thm.get_tags foo) "exported_premises")));
(* discharge, put_major_prem_first, own_major_prem *)
val _ = \<^assert> (Thm.prop_of (Exported_Premises.put_major_prem_first foo) aconv
  Logic.varify_global \<^prop>\<open>A \<Longrightarrow> LF S \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
  andalso null (Thm.get_tags (Exported_Premises.put_major_prem_first foo)));
(* "identical" / "returned as is" rows: Thm.eq_thm_strict, tags included *)
val _ = \<^assert> (Thm.eq_thm_strict (Exported_Premises.put_major_prem_first @{thm untagged}, @{thm untagged}));
val _ = \<^assert> (Thm.eq_thm_strict (Exported_Premises.put_major_prem_first @{thm LF.z0}, @{thm LF.z0}));
val _ = \<^assert> (Exported_Premises.own_major_prem foo aconv Logic.strip_assums_concl (nth (Thm.prems_of foo) 1));
val _ = \<^assert> (Exported_Premises.own_major_prem @{thm untagged} aconv Thm.major_prem_of @{thm untagged});
val _ = \<^assert> (Exported_Premises.own_major_prem @{thm LF.z0} aconv hd (Thm.prems_of @{thm LF.z0}));
val _ = \<^assert> (Thm.eq_thm_strict (Exported_Premises.discharge [] @{thm untagged}, @{thm untagged}));
val _ = \<^assert> (Thm.eq_thm_strict (Bires.kind_make_elim Bires.intro_kind foo, foo));
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind @{thm LF.fooD0}),
  Logic.varify_global \<^prop>\<open>Rc x S \<Longrightarrow> LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
val _ = \<^assert> (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind @{thm LF.z0}) aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>);
(* [exported_premises n] *)
val d0 = @{thm LF.fooD0 [exported_premises 0]};
val _ = \<^assert> (Exported_Premises.count_of d0 = 0 andalso not (has_K_tag d0)
  andalso not (AList.defined (op =) (Thm.get_tags d0) "consumes") andalso Rule_Cases.get_consumes d0 = 0);
val foo0 = @{thm LF.foo [exported_premises 0]};
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags foo0) "consumes" = SOME "2" andalso not (has_K_tag foo0));
val foo2 = @{thm LF.foo [exported_premises 2]};
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags foo2) "consumes" = SOME "2" andalso Exported_Premises.count_of foo2 = 2
  andalso Exported_Premises.strong_consumes foo2 = 0);
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind d0),
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
val _ = \<^assert> (Thm.get_tags @{thm LF.foo [exported_premises 1]} = Thm.get_tags foo);
val _ = \<^assert> (Thm.eq_thm_strict (@{thm untagged [exported_premises 0]}, @{thm untagged}));
(* [exported_premises 1] on an untagged theorem: the K tag and nothing else *)
val _ = \<^assert> (Exported_Premises.count_of @{thm untagged [exported_premises 1]} = 1
  andalso tags_without_K @{thm untagged [exported_premises 1]} = Thm.get_tags @{thm untagged});
val tc1 = @{thm tagged_c [exported_premises 1]};
val _ = \<^assert> (Exported_Premises.count_of tc1 = 1 andalso tags_without_K tc1 = Thm.get_tags @{thm tagged_c});
val _ = \<^assert> ((attr (Exported_Premises.exported_premises 5) foo ctxt; false)
  handle ERROR msg => String.isPrefix "exported_premises: count out of range" (Protocol_Message.clean_output msg));
val _ = \<^assert> ((attr (Exported_Premises.exported_premises (~1)) foo ctxt; false)
  handle ERROR msg => String.isPrefix "exported_premises: count out of range" (Protocol_Message.clean_output msg));
val _ = \<^assert> (Long_Name.base_name (#1 (Token.name_of_src (Attrib.check_src ctxt (hd (attribs_of \<^theory> "[exported_premises 1]"))))) = "exported_premises");
\<close>

(* n = K outside the block: the stock idiom dest!: works on both sides *)
lemma "LF t \<Longrightarrow> Pc t" by (auto dest!: LF.zP)
lemma "D t \<Longrightarrow> Pc t" by (auto dest!: D.zP)
declare LF.zP [dest]
declare D.zP [dest]
lemma "LF t \<Longrightarrow> Pc t" by auto
lemma "D t \<Longrightarrow> Pc t" by auto

(* the reopened block *)
declare D.z0 [dest]
ML \<open>val heavy_z0_plain = #2 (the_single (claset_entries \<^context> @{thm D.z0}));\<close>

context LF begin
declare LF.z0 [dest]
lemmas foo0 = LF.foo[exported_premises 0]
lemmas foo0c [exported_premises 0, consumes 2] = LF.foo
lemmas x1 = LF.foo_iff[THEN iffD1, exported_premises 1]
ML_val \<open>
val LFa = @{thm LF_axioms};
val (_, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.z0};
val _ = \<^assert> (Thm.prop_of plain aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>);
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (plain, heavy_z0_plain));
(* discharge *)
val d = Exported_Premises.discharge [LFa] @{thm LF.fooP};
val _ = \<^assert> (Thm.prop_of d aconv Logic.varify_global \<^prop>\<open>Pc x y\<close> andalso null (Thm.get_tags d));
(* plan line 4594: too few facts, or a fact that does not match LF ?S -- THM either way *)
val h = @{thm Qc1_ax [of c]};
val _ = \<^assert> (forall (fn facts => (Exported_Premises.discharge facts @{thm LF.fooP}; false) handle THM _ => true) [[], [h]]);
val _ = \<^assert> (null (Thm.get_tags (Exported_Premises.discharge [LFa] @{thm LF.foo})));
(* [OF] clears the tag together with consumes *)
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.foo [OF LF_axioms]} = 0 andalso null (Thm.get_tags @{thm LF.foo [OF LF_axioms]}));
(* cases rule: LF.ev.cases[exported_premises 0] chained LF_axioms h prints as without *)
val (hev, ctxte) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "h" "LF.ev S n";
val _ = \<^assert> (cases_text (run ctxte [LFa, hev] "cases rule: LF.ev.cases[exported_premises 0]" "W n") =
  cases_text (run ctxte [LFa, hev] "cases rule: LF.ev.cases" "W n"));
\<close>
end

ML \<open>
val _ = \<^assert> (not (has_K_tag @{thm LF.foo0}) andalso not (AList.defined (op =) (Thm.get_tags @{thm LF.foo0}) "consumes")
  andalso Rule_Cases.get_consumes @{thm LF.foo0} = 0);
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags @{thm LF.foo0c}) "consumes" = SOME "2");
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.x1} = 1);
\<close>

end
