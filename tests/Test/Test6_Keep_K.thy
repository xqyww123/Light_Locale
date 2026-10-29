(* Plan section 7 test 6, milestone 3's first item, second version: every system transformation
   keeps K, counted as in ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.3 (a layer that
   pastes an ordinary premise in front gives K 0).  The rows of this leaf call the transformations
   directly or through a proof block: N1 a proof block's export pastes its assumption in front
   (K 0); N2 an obtain layer adds nothing (K 1); N4 a custom export that treats theorems unevenly
   (K 0 where it pastes, K kept where not), and a custom layer that discharges the leading
   premise under an assume layer (Assumption.export K 0, layer by layer; its morphism K 1, the
   known limitation J6 of the plan's section 3.6); N9 the local copy Local_Theory.note returns in a light block for a
   theorem with hyps; N11 [setclass 1] on a theorem not in normal form keeps its case
   name; N12 the direct calls on tagged inputs that are rebuilt (Assumption.export,
   Variable.export, zero_var_indexes_list, norm_hhf_protect, Goal.norm_result, flexflex_unique,
   the beta step of instantiate_normalize_morphism, whose lambda splits a premise off the
   conclusion); N13 an untagged input comes back as the same object (Assumption.export is not a
   site row: stock Thm.join_transfer_context makes a new object even for a transferred theorem);
   N14 a light block's proof block export, read for its own major premise; N20 the redeclaration
   flag is reset inside one command; N23 instantiate_morphism and N31 eq_morphism keep K although
   the instantiation or the rewrite splits a premise off the conclusion; N24 put's range and
   idempotence; N28 the public writer Local_Theory.redeclare_result stores what the attribute
   left.  Rows that do not
   compile on the first version's tree (shift_count, redeclare_result) were ML_val commands so
   that a test-first run there could go on; like every assertion row they are ML commands now. *)
theory Test6_Keep_K
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Qc :: 'a  Rc :: 'a  Sp :: "nat \<Rightarrow> prop"
axiomatization where Qc1_ax: "Qc x"

context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
end

ML \<open>val natT = \<^typ>\<open>nat\<close>\<close>


section \<open>Proof blocks (N1, N2)\<close>

notepad
begin
  { assume hq: "Qc (0::nat)" note r = LF.foo }
  note r1 = this
  ML_prf \<open>val _ = \<^assert> (Setclass.count_of @{thm r1} = 0 andalso Thm.nprems_of @{thm r1} = 4)\<close>
next
  { obtain n :: nat where "Qc n" by (rule that, rule Qc1_ax)
    note r = LF.foo }
  note r2 = this
  ML_prf \<open>val _ = \<^assert> (Setclass.count_of @{thm r2} = 1 andalso Thm.nprems_of @{thm r2} = 3)\<close>
end


section \<open>Custom exports (N4)\<close>

(* a layer whose export puts its assumption only in front of theorems whose conclusion mentions
   Rc: the K 1 theorem about Rc gets K 0 (an ordinary premise pasted in front), LF.foo stays K 1 *)
ML \<open>
fun mentions_Rc th = exists_Const (fn (c, _) => c = \<^const_name>\<open>Rc\<close>) (Thm.concl_of th);
fun uneven_export _ asms = (fn th => if mentions_Rc th then Drule.implies_intr_list asms th else th, I);
val tRc =
  Thm.assume \<^cprop>\<open>Rc (x::nat)\<close> |> Thm.implies_intr \<^cprop>\<open>Rc (x::nat)\<close>
  |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val (_, ctxt_u) = Assumption.add_assms uneven_export [\<^cprop>\<open>Qc (5::nat)\<close>] \<^context>;
\<close>
ML \<open>local
val th = Assumption.export ctxt_u \<^context> tRc;
val _ = \<^assert> (Thm.nprems_of th = 3 andalso Setclass.count_of th = 0);
in end\<close>
ML \<open>local
val th = Assumption.export ctxt_u \<^context> @{thm LF.foo};
val _ = \<^assert> (Thm.nprems_of th = 3 andalso Setclass.count_of th = 1);
in end\<close>
(* a custom inner layer that discharges the first premise (it becomes a hyp) under an outer assume
   layer that puts its assumption in front.  Assumption.export goes layer by layer: one premise
   fewer takes K 1 to 0, then Qc 7 is pasted on an untagged theorem, K 0.  Through the export
   morphism the fallback restore_counts compares only the morphism's input and output (three
   premises each) and writes K 1 back: the known limitation J6 (plan section 3.6), to become 0
   when K 0 and "unknown" are told apart *)
ML \<open>
fun discharging_export _ _ = (drop_first, I);
val (_, ctxt_o) = Assumption.add_assumes [\<^cprop>\<open>Qc (7::nat)\<close>] \<^context>;
val (_, ctxt_i) = Assumption.add_assms discharging_export [\<^cprop>\<open>Qc (6::nat)\<close>] ctxt_o;
val fooS = Setclass.put 1 (Variable.import_vars \<^context> @{thm LF.foo});
\<close>
ML \<open>local
val th = Assumption.export ctxt_i \<^context> fooS;
val _ = \<^assert> (Thm.nprems_of th = 3 andalso Setclass.count_of th = 0);
in end\<close>
ML \<open>local
val [th] = Morphism.fact (Assumption.export_morphism ctxt_i \<^context>) [fooS];
val _ = \<^assert> (Thm.nprems_of th = 3 andalso Setclass.count_of th = 1);
in end\<close>


section \<open>The local copy of a theorem with hyps in a light block (N9)\<close>

context LF begin
ML \<open>local
val th = Setclass.put 1 (Thm.implies_intr \<^cprop>\<open>Qc (0::nat)\<close> @{thm LF_axioms});
val _ = \<^assert> (not (null (Thm.hyps_of th)));
val ((_, [th']), _) = Local_Theory.note ((\<^binding>\<open>n9\<close>, []), [th]) \<^context>;
val _ = \<^assert> (Setclass.count_of th' = 1);
in end\<close>
end


section \<open>The attribute on a theorem not in normal form (N11)\<close>

ML \<open>local
val th =
  Thm.forall_intr_vars @{thm conjI} |> Thm.implies_intr \<^cprop>\<open>LF S\<close>
  |> Setclass.put 1 |> Rule_Cases.name ["a"];
val _ = \<^assert> (not (Drule.is_norm_hhf {protect = false} (Thm.prop_of th)));
val th' = attr (Attrib.attribute_cmd \<^context> (hd (attribs_of \<^theory> "[setclass 1]"))) th \<^context>;
val _ = \<^assert> (Setclass.count_of th' = 1 andalso map (#1 o #1) (#1 (Rule_Cases.get th')) = ["a"]);
in end\<close>


section \<open>Direct calls on tagged inputs that are rebuilt (N12)\<close>

ML \<open>local
val ([hq], ctxt1) = Assumption.add_assumes [\<^cprop>\<open>Qc (3::nat)\<close>] \<^context>;
val th = hq |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val th' = Assumption.export ctxt1 \<^context> th;
val _ = \<^assert> (Thm.nprems_of th' = 2 andalso Setclass.count_of th' = 0);
in end\<close>
ML \<open>local
val ctxt1 = fix_in \<^context> [("x", natT)];
val th = Thm.reflexive \<^cterm>\<open>x :: nat\<close> |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val [th'] = Variable.export ctxt1 \<^context> [th];
val _ = \<^assert> (not (Thm.eq_thm_prop (th', th)) andalso Setclass.count_of th' = 1);
in end\<close>
ML \<open>local
val th = Setclass.put 1 (Thm.incr_indexes 1 @{thm LF.foo});
val _ = \<^assert> (Thm.maxidx_of th = 1);
val [th'] = Drule.zero_var_indexes_list [th];
val _ = \<^assert> (Thm.maxidx_of th' = 0 andalso Setclass.count_of th' = 1);
in end\<close>
ML \<open>local
val th = Thm.forall_intr_vars @{thm conjI} |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val th' = Raw_Simplifier.norm_hhf_protect \<^context> th;
val _ = \<^assert> (Thm.nprems_of th' = 3 andalso Setclass.count_of th' = 1);
in end\<close>
ML \<open>local
val th = Setclass.put 1 (Thm.incr_indexes 1 @{thm LF.foo});
val th' = Goal.norm_result \<^context> th;
val _ = \<^assert> (Thm.maxidx_of th' = 0 andalso Setclass.count_of th' = 1);
in end\<close>
(* a theorem with a flex-flex pair: refl resolved against ?F ?a = ?G ?b *)
ML \<open>
val ct = Thm.cterm_of \<^context>
  (HOLogic.mk_Trueprop (HOLogic.mk_eq
    (Var (("F", 0), natT --> natT) $ Var (("a", 0), natT), Var (("G", 0), natT --> natT) $ Var (("b", 0), natT))));
val flex = Seq.hd (Thm.biresolution NONE false [(false, @{thm refl})] 1 (Thm.trivial ct));
val flex_tagged = flex |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
\<close>
ML \<open>val _ = \<^assert> (not (null (Thm.tpairs_of flex_tagged)))\<close>
ML \<open>local
val th' = Drule.flexflex_unique (SOME \<^context>) flex_tagged;
val _ = \<^assert> (null (Thm.tpairs_of th') andalso Setclass.count_of th' = 1);
in end\<close>
(* the beta step: a lambda for a prop-valued parameter whose body is an implication splits a
   premise off the conclusion (Thm.instantiate_frees does not beta-reduce); K 1 stays, where the
   fallback alone would write K 0 (a premise more) *)
ML \<open>local
val cP = \<^cprop>\<open>PROP P (0::nat)\<close>;
val th = Thm.assume cP |> Thm.implies_intr cP |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val phi = Element.instantiate_normalize_morphism
  (TFrees.empty,
   Frees.make1 (("P", natT --> propT), \<^cterm>\<open>\<lambda>n::nat. (PROP Sp n \<Longrightarrow> PROP Sp n)\<close>));
val [th'] = Morphism.fact phi [th];
val _ = \<^assert> (Thm.prop_of th' aconv
  \<^prop>\<open>LF S \<Longrightarrow> (PROP Sp 0 \<Longrightarrow> PROP Sp 0) \<Longrightarrow> PROP Sp 0 \<Longrightarrow> PROP Sp 0\<close>);
val _ = \<^assert> (Thm.nprems_of th' = 3 andalso Setclass.count_of th' = 1);
in end\<close>


section \<open>Untagged inputs come back as the same object (N13)\<close>

ML \<open>local
val u = @{thm TrueI} and v = @{thm conjI};
val _ = \<^assert> (pointer_eq (Setclass.keep_count u v, v));
in end\<close>
ML \<open>local
val u = @{thm TrueI} and v = @{thm conjI};
val _ = \<^assert> (pointer_eq (Setclass.shift_count u v, v));
in end\<close>
ML \<open>local
val th = @{thm conjI};
val [th'] = Variable.export \<^context> \<^context> [th];
val _ = \<^assert> (pointer_eq (th', th));
in end\<close>
ML \<open>local
val th = @{thm LF.foo};
val [th'] = Variable.export \<^context> \<^context> [th];
val _ = \<^assert> (pointer_eq (th', th));
in end\<close>


section \<open>A light block's proof block (N14)\<close>

context LF begin
notepad
begin
  { assume hq: "Qc (0::nat)" note r = LF.foo }
  note r14 = this
  ML_prf \<open>local
  val th = @{thm r14};
  val _ = \<^assert> (Setclass.count_of th = 0);
  val _ = \<^assert> (same_shape (Setclass.own_major_prem th, Logic.varify_global \<^prop>\<open>Qc (0::nat)\<close>));
   in end\<close>
end
end


section \<open>The redeclaration flag is reset within one command (N20)\<close>

context LF begin
local_setup \<open>
  Specification.theorems "" [((\<^binding>\<open>r1\<close>, []), [(@{thms conjI}, [])])] [] false #> snd #>
  Local_Theory.note ((\<^binding>\<open>r2\<close>, []), @{thms conjI}) #> snd\<close>
end
ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.r2} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q\<close>
  andalso Setclass.count_of @{thm LF.r2} = 1);
\<close>


section \<open>instantiate_morphism (N23)\<close>

ML \<open>local
val th = Setclass.put 1 @{lemma "PROP Q \<Longrightarrow> PROP P \<Longrightarrow> PROP P" by assumption};
val phi = Morphism.instantiate_morphism
  (TVars.empty, Vars.make1 ((("P", 0), propT), \<^cprop>\<open>PROP A \<Longrightarrow> PROP B\<close>));
val [th'] = Morphism.fact phi [th];
val _ = \<^assert> (Thm.nprems_of th' = 3 andalso Setclass.count_of th' = 1);
in end\<close>


section \<open>eq_morphism (N31)\<close>

(* a rewrites equation whose right-hand side is an implication splits a premise off the
   conclusion (and rewrites the same premise): K 1 stays, where the fallback alone would write K 0.
   The equation is assumed, since @{lemma} would make its left-hand side schematic *)
ML \<open>local
val cQ = \<^cprop>\<open>PROP Sp 0\<close>;
val th = Thm.assume cQ |> Thm.implies_intr cQ |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Setclass.put 1;
val eq = Thm.assume \<^cprop>\<open>PROP Sp 0 \<equiv> (PROP A \<Longrightarrow> PROP B)\<close>;
val phi = the (Element.eq_morphism \<^context> [eq]) |> Morphism.set_context' \<^context>;
val [th'] = Morphism.fact phi [th];
val _ = \<^assert> (Thm.nprems_of th' = 3 andalso Setclass.count_of th' = 1);
in end\<close>


section \<open>put (N24)\<close>

ML \<open>val _ = \<^assert> (not (has_K_tag (Setclass.put 3 @{thm conjI})))\<close>
ML \<open>val _ = \<^assert> (not (has_K_tag (Setclass.put ~1 @{thm conjI})))\<close>
ML \<open>local
val th = @{thm LF.foo};
val _ = \<^assert> (pointer_eq (Setclass.put 1 th, th));
in end\<close>
ML \<open>local
val th = Thm.tag_rule (Setclass.setclass_tagN, "3") @{thm conjI};
val _ = \<^assert> (not (has_K_tag (Setclass.put 3 th)));
in end\<close>


section \<open>The public writer redeclare_result (N28)\<close>

(* a rule attribute evaluated inside light_notes' own partial evaluation leaves conjI with
   index-1 variables and a tag t; a redeclaration stores both copies as that theorem *)
context LF begin
ML \<open>local
val index_and_tag = Thm.rule_attribute [] (fn _ => Thm.incr_indexes 1 #> Thm.tag_rule ("t", "v"));
val (res, lthy') =
  Local_Theory.redeclare_result
    (Local_Theory.notes
      [((\<^binding>\<open>yr\<close>, [Attrib.internal \<^here> (K index_and_tag)]), [(@{thms conjI}, [])])])
    \<^context>;
val [(_, [loc])] = res;
val thy_copy = Proof_Context.get_thm (Proof_Context.init_global (Proof_Context.theory_of lthy')) "LF.yr";
fun as_left th = AList.lookup (op =) (Thm.get_tags th) "t" = SOME "v" andalso Thm.maxidx_of th = 1;
val _ = \<^assert> (as_left loc andalso as_left thy_copy);
in end\<close>
end

end
