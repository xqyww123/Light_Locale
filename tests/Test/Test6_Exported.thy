(* Plan section 7 test 6, the Setclass unit rows (plan lines 4576-4601, 4604-4625,
   4629-4645): count_of, get_consumes and the K-offset consumes/default_consumes on
   untagged and tagged theorems, which attributes keep the tag, put, tag-string sharing, discharge,
   put_major_prem_first, own_major_prem, kind_make_elim, [dest] on a rule without own premises
   (fails in the block, accepted on the theory copy and read back as LF ?S ==> ...), the n = K
   usage outside the block, [setclass n] in all its forms including the out-of-range
   error, and the in-block writings foo0 / x1 / e1; the activation site under hand-made
   morphisms and the direct rows of Morphism.morphism's fallback (milestone 3's first item,
   second version). *)
theory Test6_Exported
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

consts Rc :: 'a  Sc :: 'a  Pc :: 'a  Qc :: 'a  c :: 'a
axiomatization where Sc_ax: "Sc x" and Pc_ax: "Pc x y" and Pc1_ax: "Pc x" and Qc1_ax: "Qc x"

lemma untagged: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma tagged_c [consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)

context D begin
lemma fooQ: "Qc x \<Longrightarrow> Pc x y" by (rule Pc_ax)
lemma z0: "Sc x" by (rule Sc_ax)
lemma zP: "Pc S" by (rule Pc1_ax)
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML \<open>val _ = \<^assert> (not (can (fn () => theorem_in \<^context> (Binding.name "z") "[dest]" "Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax})) ()))\<close>
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
ML \<open>val _ = \<^assert> (not (can (fn () => theorem_in \<^context> (Binding.name "z") "[dest]" "Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax})) ()))\<close>
(* e1 [setclass 3] on a one-premise block form: out of range; [setclass 2] on
   two premises: accepted; the theory copy keeps the hand-written K plus the one premise the
   export puts in front, K 3 (second version); e1 is a mechanism fixture, not a user scenario *)
ML \<open>local
fun insert_assume ctxt i = Method.insert_tac ctxt @{thms LF_axioms} i THEN assume_tac ctxt i;
val _ = \<^assert> ((theorem_in \<^context> (Binding.name "e1") "[setclass 3]" "A \<Longrightarrow> A" insert_assume; false)
  handle ERROR msg => String.isPrefix "setclass: count out of range" (Protocol_Message.clean_output msg));
in end\<close>
lemma e1 [setclass 2]: "A \<Longrightarrow> A \<Longrightarrow> A"
  apply (insert LF_axioms) apply assumption done
(* the same-row note with cases pred, up to K with the twin's *)
ML \<open>local
val r = #1 (note_in \<^context> "r" "[cases pred: Qc]" @{thm LF.fooQ [of _ c]});
val _ = \<^assert> (diff_K 1 (r, heavy_r));
(* the notes in a proof in the block (plan lines 4629-4632), driven through note_in -- the
   Proof_Context.note_thmss an in-proof note runs, the attributes parsed from their text: THEN
   clears the tag, [setclass 1] writes it back *)
val (r, ctxt_r) = note_in \<^context> "r" "[THEN conjunct1]" @{thm LF.foo};
val _ = \<^assert> (Setclass.count_of r = 0);
val (r', _) = note_in ctxt_r "r'" "[setclass 1]" r;
val _ = \<^assert> (Setclass.count_of r' = 1 andalso not (AList.defined (op =) (Thm.get_tags r') "consumes")
  andalso Rule_Cases.get_consumes r' = 1 andalso Setclass.strong_consumes r' = 0);
(* THEN renames to conjunct1's ?P ?Q: compared up to variable names *)
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind r'),
  Logic.varify_global \<^prop>\<open>A \<Longrightarrow> LF S \<Longrightarrow> B \<Longrightarrow> (A \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
in end\<close>
end

ML \<open>
val _ = \<^assert> (Setclass.count_of @{thm LF.e1} = 3 andalso
  Thm.prop_of @{thm LF.e1} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A\<close>);
\<close>

ML \<open>
val ctxt = \<^context>;
val fooP = @{thm LF.fooP} and foo = @{thm LF.foo};
(* count_of, get_consumes *)
val _ = \<^assert> (Setclass.count_of @{thm untagged} = 0);
val _ = \<^assert> (Setclass.count_of fooP = 1 andalso Rule_Cases.get_consumes fooP = 1
  andalso not (AList.defined (op =) (Thm.get_tags fooP) "consumes"));
val rot = @{thm LF.bad [rotated]};
val _ = \<^assert> (Setclass.count_of rot = 0 andalso Rule_Cases.get_consumes rot = 0);
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
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags f1) "consumes" = SOME "2" andalso Setclass.count_of f1 = 1);
val f2 = attr (Rule_Cases.consumes (~1)) foo ctxt;
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags f2) "consumes" = SOME "2");
val p1 = Rule_Cases.default_consumes 1 fooP;
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags p1) "consumes" = SOME "2");
val _ = \<^assert> (Thm.eq_thm_strict (Rule_Cases.default_consumes 1 foo, foo));
(* get_consumes: the max of K and the recorded value *)
val _ = \<^assert> (Rule_Cases.get_consumes fooP = 1);
val _ = \<^assert> (Rule_Cases.get_consumes @{thm LF.fooP [setclass 0]} = 0);
val p0 = Rule_Cases.put_consumes (SOME 0) fooP;
val _ = \<^assert> (Rule_Cases.get_consumes p0 = 1 andalso Setclass.strong_consumes p0 = 0);
(* which attributes keep the tag *)
val _ = \<^assert> (Setclass.count_of @{thm LF.fooP [of _ c]} = 1);
val _ = \<^assert> (Setclass.count_of @{thm LF.fooP [where x = c]} = 1);
val _ = \<^assert> (Setclass.count_of @{thm LF.fooB [params a b]} = 1);
val _ = \<^assert> (Setclass.count_of @{thm LF.foo [THEN conjunct1]} = 0 andalso null (Thm.get_tags @{thm LF.foo [THEN conjunct1]}));
val _ = \<^assert> (Setclass.count_of @{thm LF.foo [rotated]} = 0 andalso null (Thm.get_tags @{thm LF.foo [rotated]}));
val _ = \<^assert> (Setclass.count_of @{thm LF.fooP [simplified]} = 1);
(* put *)
val _ = \<^assert> (Thm.eq_thm_strict (Setclass.put 0 @{thm untagged}, @{thm untagged}));
val fp0 = Setclass.put 0 foo;
val _ = \<^assert> (not (has_K_tag fp0) andalso AList.lookup (op =) (Thm.get_tags fp0) "consumes" = SOME "2"
  andalso tags_without_K foo = Thm.get_tags fp0);
val up1 = Setclass.put 1 @{thm untagged};
val _ = \<^assert> (Setclass.count_of up1 = 1 andalso not (AList.defined (op =) (Thm.get_tags up1) "consumes"));
(* the tag strings of two freshly stored theorems are shared *)
val _ = \<^assert> (pointer_eq (the (AList.lookup (op =) (Thm.get_tags fooP) Setclass.setclass_tagN),
  the (AList.lookup (op =) (Thm.get_tags foo) Setclass.setclass_tagN)));
(* discharge, put_major_prem_first, own_major_prem *)
val _ = \<^assert> (Thm.prop_of (Setclass.put_major_prem_first foo) aconv
  Logic.varify_global \<^prop>\<open>A \<Longrightarrow> LF S \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
  andalso null (Thm.get_tags (Setclass.put_major_prem_first foo)));
(* "identical" / "returned as is" rows: Thm.eq_thm_strict, tags included *)
val _ = \<^assert> (Thm.eq_thm_strict (Setclass.put_major_prem_first @{thm untagged}, @{thm untagged}));
val _ = \<^assert> (Thm.eq_thm_strict (Setclass.put_major_prem_first @{thm LF.z0}, @{thm LF.z0}));
val _ = \<^assert> (Setclass.own_major_prem foo aconv Logic.strip_assums_concl (nth (Thm.prems_of foo) 1));
val _ = \<^assert> (Setclass.own_major_prem @{thm untagged} aconv Thm.major_prem_of @{thm untagged});
val _ = \<^assert> (Setclass.own_major_prem @{thm LF.z0} aconv hd (Thm.prems_of @{thm LF.z0}));
val _ = \<^assert> (Thm.eq_thm_strict (Setclass.discharge [] @{thm untagged}, @{thm untagged}));
val _ = \<^assert> (Thm.eq_thm_strict (Bires.kind_make_elim Bires.intro_kind foo, foo));
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind @{thm LF.fooD0}),
  Logic.varify_global \<^prop>\<open>Rc x S \<Longrightarrow> LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
val _ = \<^assert> (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind @{thm LF.z0}) aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>);
(* [setclass n] *)
val d0 = @{thm LF.fooD0 [setclass 0]};
val _ = \<^assert> (Setclass.count_of d0 = 0 andalso not (has_K_tag d0)
  andalso not (AList.defined (op =) (Thm.get_tags d0) "consumes") andalso Rule_Cases.get_consumes d0 = 0);
val foo0 = @{thm LF.foo [setclass 0]};
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags foo0) "consumes" = SOME "2" andalso not (has_K_tag foo0));
val foo2 = @{thm LF.foo [setclass 2]};
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags foo2) "consumes" = SOME "2" andalso Setclass.count_of foo2 = 2
  andalso Setclass.strong_consumes foo2 = 0);
val _ = \<^assert> (same_shape (Thm.prop_of (Bires.kind_make_elim Bires.dest_kind d0),
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
val _ = \<^assert> (Thm.get_tags @{thm LF.foo [setclass 1]} = Thm.get_tags foo);
val _ = \<^assert> (Thm.eq_thm_strict (@{thm untagged [setclass 0]}, @{thm untagged}));
(* [setclass 1] on an untagged theorem: the K tag and nothing else *)
val _ = \<^assert> (Setclass.count_of @{thm untagged [setclass 1]} = 1
  andalso tags_without_K @{thm untagged [setclass 1]} = Thm.get_tags @{thm untagged});
val tc1 = @{thm tagged_c [setclass 1]};
val _ = \<^assert> (Setclass.count_of tc1 = 1 andalso tags_without_K tc1 = Thm.get_tags @{thm tagged_c});
val _ = \<^assert> ((attr (Attrib.attribute_cmd ctxt (hd (attribs_of \<^theory> "[setclass 5]"))) foo ctxt; false)
  handle ERROR msg => String.isPrefix "setclass: count out of range" (Protocol_Message.clean_output msg));
val _ = \<^assert> ((attr (Attrib.attribute_cmd ctxt (hd (attribs_of \<^theory> "[setclass -1]"))) foo ctxt; false)
  handle ERROR msg => String.isPrefix "setclass: count out of range" (Protocol_Message.clean_output msg));
val _ = \<^assert> (Long_Name.base_name (#1 (Token.name_of_src (Attrib.check_src ctxt (hd (attribs_of \<^theory> "[setclass 1]"))))) = "setclass");
\<close>

(* The activation site Element.transform_ctxt with hand-made morphisms: (a) under the identity
   morphism an untagged theorem, or one tagged with a literal "0", comes back as the same value
   (no map_tags); (b) an untagged input through a morphism that puts a premise in front comes back
   with three premises and no K.  Then the fallback of Morphism.morphism (second version), called
   directly through Morphism.fact on morphisms whose parts clear the tags: (a') when no input has
   K the outputs come back as the same objects; (b') a premise pasted in front gives K 0 for each
   theorem of a list mixing K 1 and K 0, checked pair by pair (proposition, K); (c) a part that
   clears the tags and keeps the premise count: K unchanged; (d1) a part that drops one leading
   premise of a K 2 theorem: K 1; (d2) one that drops more than K: no K; (e) a tag-clearing part
   and instantiate_frees_morphism of a prop parameter, in both orders: K 1 and three premises;
   (f) parts that change the list's length: no exception, the outputs returned as they are. *)
ML \<open>
fun transform_facts phi ths =
  (case Element.transform_ctxt phi (Element.Notes ("", [(Binding.empty_atts, [(ths, [])])])) of
    Element.Notes (_, [(_, [(ths', _)])]) => ths'
  | _ => raise Fail "transform_facts");
val add_prem = Thm.implies_intr \<^cprop>\<open>Qc (2::nat)\<close>;
val adding = Morphism.thm_morphism "adding" add_prem;
\<close>
ML \<open>local
(* each @{thm} occurrence is its own transferred value, so the input is bound once *)
val u = @{thm untagged};
val th0 = Thm.tag_rule (Setclass.setclass_tagN, "0") u;
val [th0', th'] = transform_facts Morphism.identity [th0, u];
val _ = \<^assert> (pointer_eq (th0', th0) andalso pointer_eq (th', u));
in end\<close>
ML \<open>local
val [th'] = transform_facts adding [@{thm untagged}];
val _ = \<^assert> (Thm.nprems_of th' = 3 andalso not (has_K_tag th'));
in end\<close>
(* the fallback's direct rows *)
ML \<open>
(*a part that clears the tags and keeps the premises*)
val untag = Morphism.thm_morphism "untag" (Thm.map_tags (K []));
(*parts that discharge one or two leading premises (inference rules: the tags go)*)
val dropping = Morphism.thm_morphism "dropping" drop_first;
val dropping2 = Morphism.thm_morphism "dropping2" (drop_first #> drop_first);
fun prop_K th = (Thm.prop_of th, Setclass.count_of th);
\<close>
ML \<open>local
(* (a') no input has K: the outputs come back as the same objects *)
val ths = [@{thm untagged}, @{thm tagged_c}];
val outs = map add_prem ths;
val _ = \<^assert> (eq_list pointer_eq (Morphism.fact (Morphism.fact_morphism "made" (K outs)) ths, outs));
in end\<close>
ML \<open>local
(* (b') a premise pasted in front: K 0, pair by pair *)
val fooP = @{thm LF.fooP} and u = @{thm untagged};
val outs = Morphism.fact adding [fooP, u];
val _ = \<^assert> (map prop_K outs =
  [(Logic.mk_implies (\<^prop>\<open>Qc (2::nat)\<close>, Thm.prop_of fooP), 0),
   (Logic.mk_implies (\<^prop>\<open>Qc (2::nat)\<close>, Thm.prop_of u), 0)]);
in end\<close>
ML \<open>local
(* (c) premises unchanged: K unchanged *)
val [f'] = Morphism.fact untag [@{thm LF.foo}];
val _ = \<^assert> (Setclass.count_of f' = 1);
in end\<close>
ML \<open>local
(* (d1) one leading premise dropped from a K 2 theorem: K 1 *)
val k2 = Setclass.put 2 (Variable.import_vars \<^context> @{thm LF.foo});
val [d'] = Morphism.fact dropping [k2];
val _ = \<^assert> (Thm.nprems_of d' = 2 andalso Setclass.count_of d' = 1);
in end\<close>
ML \<open>local
(* (d2) more premises dropped than K: no K *)
val [d'] = Morphism.fact dropping2 [Setclass.put 1 (Variable.import_vars \<^context> @{thm LF.foo})];
val _ = \<^assert> (Thm.nprems_of d' = 1 andalso not (has_K_tag d'));
in end\<close>
ML \<open>local
(* (e) a tag-clearing part and the instantiation of a prop parameter T := (A ==> B), both orders:
   the premise split off the conclusion at the end is not counted, K 1 and three premises *)
val cT = \<^cprop>\<open>PROP T\<close>;
val th = Thm.implies_intr cT (Thm.assume cT) |> Thm.implies_intr \<^cprop>\<open>Qc (0::nat)\<close> |> Setclass.put 1;
val inst = Morphism.instantiate_frees_morphism
  (TFrees.empty, Frees.make1 (("T", propT), \<^cprop>\<open>PROP A \<Longrightarrow> PROP B\<close>));
val [e1] = Morphism.fact (untag $> inst) [th];
val [e2] = Morphism.fact (inst $> untag) [th];
val _ = \<^assert> (forall (fn e => Setclass.count_of e = 1 andalso Thm.nprems_of e = 3) [e1, e2]);
in end\<close>
ML \<open>local
(* (f) parts that change the list's length *)
val u = @{thm untagged} and k = @{thm LF.foo};
val splitting = Morphism.fact_morphism "splitting" (fn [a, b] => [a, a, b] | ths => ths);
val outs = Morphism.fact splitting [u, k];
val _ = \<^assert> (length outs = 3 andalso pointer_eq (nth outs 2, k));
val dropping_all = Morphism.fact_morphism "dropping_all" (K []);
val _ = \<^assert> (null (Morphism.fact dropping_all [k]));
in end\<close>

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
lemmas foo0 = LF.foo[setclass 0]
lemmas foo0c [setclass 0, consumes 2] = LF.foo
lemmas x1 = LF.foo_iff[THEN iffD1, setclass 1]
(* the usage sentence (plan line 873): [setclass n] after a mixed attribute on a lemma
   or lemmas line is stock's error; after a registration attribute it is accepted without a
   message, the attribute before it having acted on the theorem without K -- the elim rule
   registered for LF.foo has major premise LF ?S; the control, the minimal pair of the same
   attribute list in the other order, LF.fooQ [setclass 0, setclass 1, elim]:
   Qc ?x (another fact, since Classical drops a second registration of the same one) *)
ML \<open>
val _ = fails_prefix "Mixed dynamic attribute followed by static rule" (fn () =>
  theorem_in \<^context> (Binding.name "m1") "[consumes 1, setclass 1]" "A \<Longrightarrow> A" assume_tac);
val _ = fails_prefix "Mixed dynamic attribute followed by static rule" (fn () =>
  lemmas_in \<^context> "m2" "LF.foo" "[consumes 1, setclass 1]");
\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.foo" "[setclass 0, elim, setclass 1]")
  in \<^assert> (null w); lthy' end\<close>
declare LF.fooQ [setclass 0, setclass 1, elim]
ML \<open>local
val ctxt = \<^context>;
val (_, silent) = claset_rule ctxt Bires.elim_kind @{thm LF.foo};
val (_, control) = claset_rule ctxt Bires.elim_kind @{thm LF.fooQ};
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt (Thm.major_prem_of silent));
val _ = \<^assert> (same_shape (Thm.major_prem_of control, Logic.varify_global \<^prop>\<open>Qc x\<close>));
in end\<close>
ML \<open>local
val LFa = @{thm LF_axioms};
val (_, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.z0};
val _ = \<^assert> (Thm.prop_of plain aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (Sc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>);
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (plain, heavy_z0_plain));
(* discharge *)
val d = Setclass.discharge [LFa] @{thm LF.fooP};
val _ = \<^assert> (Thm.prop_of d aconv Logic.varify_global \<^prop>\<open>Pc x y\<close> andalso null (Thm.get_tags d));
(* plan line 4594: too few facts, or a fact that does not match LF ?S -- THM either way *)
val h = @{thm Qc1_ax [of c]};
val _ = \<^assert> (forall (fn facts => (Setclass.discharge facts @{thm LF.fooP}; false) handle THM _ => true) [[], [h]]);
val _ = \<^assert> (null (Thm.get_tags (Setclass.discharge [LFa] @{thm LF.foo})));
(* [OF] clears the tag together with consumes *)
val _ = \<^assert> (Setclass.count_of @{thm LF.foo [OF LF_axioms]} = 0 andalso null (Thm.get_tags @{thm LF.foo [OF LF_axioms]}));
(* cases rule: LF.ev.cases[setclass 0] chained LF_axioms h prints as without *)
val (hev, ctxte) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "h" "LF.ev S n";
val _ = \<^assert> (cases_text (run ctxte [LFa, hev] "cases rule: LF.ev.cases[setclass 0]" "W n") =
  cases_text (run ctxte [LFa, hev] "cases rule: LF.ev.cases" "W n"));
in end\<close>
end

(* foo0 is a redeclaration whose export changes nothing: stored as the attribute's result itself,
   no K, its consumes "2" kept (second version) *)
ML \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.foo0}, foo0) andalso not (has_K_tag @{thm LF.foo0})
  andalso Rule_Cases.get @{thm LF.foo0} = Rule_Cases.get foo0);
\<close>
ML \<open>
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags @{thm LF.foo0c}) "consumes" = SOME "2");
val _ = \<^assert> (Setclass.count_of @{thm LF.x1} = 1);
\<close>

end
