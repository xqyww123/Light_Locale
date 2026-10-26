(* Plan section 7 test 6, a heavy locale importing a light one (plan lines 4740-4749; REV19-14,
   section 11 (39); milestone 3's first item, section 11 (40)): locale H = LF + fixes z assumes
   hz.  In H's block the bare lemmas foo2 [case_names a b] = LF.foo keeps the K tag (the local half
   of thm_definition puts it back with keep_count after its inference rules clear every tag), so case a
   lands on A as in the heavy twin Hh's block; the bare declare LF.foo [elim] registers a rule
   whose major premise is A; the compensating spelling LF.foo[OF LF_axioms] is the bare copy with
   its exported premise discharged (K 0, as the twin); the block re-opened and the theory copies
   after interpretation I: H t 0 keep K through the activation morphisms; "using LF_axioms h
   proof cases" prints the twin's cases (pinned to ip's z / s), the bare "using h proof cases"
   falls to case_split, after the interpretation the same pair at theory level, the cases
   compared term by term with the twin's interpretation Ih (the instance names differ, LF.ip t
   against D.ip t: twin_names).  thm_definition is shared by every named target: a class
   block, a theory-level anonymous block and a heavy importer's header notes clause (H2) keep K
   alike.
   Milestone 3's first item: every copy a morphism makes of a K-tagged theorem gets K back plus
   d, the number of premises the morphism puts in front.  The record copy (standard_facts):
   foo3 K 2 under a nested assumes layer, foo4 K 3 under two, nh4 K 1 under a fixes-only layer,
   h3 K 1 on a lemma line although the record copy renumbers the variables THEN conjunct1 left
   with index > 0 (h5 on a lemmas line, the control), nh2 likewise with a statement-level for
   clause, h3c the same in a class block; the outer copies (standard_notes): foo4 K 2 between its
   two ends; the activated copies (Element.transform_ctxt): J.foo2 K 2 behind the block
   assumption of global_interpretation J inside context fixes x assumes hx (K 1 inside that
   block), case a on A, the elim registration H's block made for LF.foo replayed through J with
   major premise A, J.nh1 K 2 by the replay of a fact added after J, I.foo2 and I.nh1 K 1 with
   d = 0.  A theorem re-declared in a light block without hyps is stored as it is, whatever its
   K (second version: re-declaration and no hyps is the whole criterion): b = J.foo2 keeps its
   statement with K 2, c = I.h3 keeps its statement without LF ?S in front.
   put checks the range: a K-tagged input not in HHF form keeps K = 1 on the local copy
   (foo_nhhf, reachable from ML only), a hand-written K beyond the premise count is dropped to 0
   on the local copy Local_Theory.note returns (k3).
   Second version (every system transformation keeps K, so the theory copies carry it too): H2.foo2
   K 2, H.foo2 K 2, H.foo3 K 3, H.foo4 K 4; the class block's theory copy Cz.foo2c K 2 behind
   class.Cz ?zc, Cz.h3c without K (its K came from the lemma line's attribute, which the class
   target strips); bundle bJ's entry of J.foo2 K 2 (the bundle target renumbers its index-1
   variables); the SORT_CONSTRAINT rows in H: a nested assumes layer whose only assumption is a
   sort constraint adds nothing to K on any copy (r8, r8t), a layer with Qc c beside it adds one
   (r8m), the theory-level dest rule made from such a layer has major premise A (replayed through
   I: key K 2), and a proof block assuming a sort constraint exports LF.foo with K 1 (r8p).
   [exported_premises n] tags the HHF normal form, so written last on a lemmas line after
   an attribute that leaves a non-HHF result it keeps K (nh1; [exported_premises 2] on the same
   input: the range counts the normal form), and when the normalisation rebuilds the theorem it
   puts the input's Rule_Cases tags back (th3: consumes 1 kept under K 2; case_names a kept, also
   with n = 0).  The row of plan lines 4748-4749 is dropped (section 11, item (27)). *)
theory Test6_Heavy_Imports
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"
axiomatization t :: "nat ring" where t: "cring t"

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
fun major_light ctxt th = Light_Locale_Axiom_Facts.is_light_prop ctxt (Thm.major_prem_of th);
(*a light copy against its heavy twin: Rule_Cases equal up to the K the row states, the own
  premises and the conclusion the twin's statement, the first own premise not the light predicate*)
fun light_copy ctxt k (thl, thh) =
  diff_K k (thl, thh) andalso
  same_shape (Logic.list_implies (Exported_Premises.own_prems thl, Thm.concl_of thl), Thm.prop_of thh) andalso
  not (Light_Locale_Axiom_Facts.is_light_prop ctxt (hd (Exported_Premises.own_prems thl)));
(*a light elim registration against the twin's: K = 1 on the key, the derived rule's major
  premise is A as the twin's*)
fun light_elim ctxt ((key, plain), (hkey, hplain)) =
  Exported_Premises.count_of key = 1 andalso not (major_light ctxt plain) andalso
  same_shape (Thm.major_prem_of plain, Thm.major_prem_of hplain) andalso diff_K 1 (key, hkey);
\<close>

context D begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end
context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
(* a fact without own premises, for the SORT_CONSTRAINT rows *)
lemma fooT: "Pc S (0::nat)" by (rule Pc_ax)
end

locale Hh = D + fixes z :: nat assumes hz: "Qc z"
context Hh begin
lemmas foo2 [case_names a b] = foo
declare foo [elim]
ML \<open>
val heavy_foo2 = @{thm foo2};
val heavy_foo_elim = claset_rule \<^context> Bires.elim_kind @{thm foo};
val heavy_H_cases =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_text st end;
\<close>
end
interpretation Ih: Hh "UP t" t 0 by (rule Hh.intro) (rule D.intro, simp_all add: UP_cring_def t Hh_axioms_def Qc1_ax)
ML \<open>
val heavy_interp =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "D.ip t n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_terms canonical_vars st end;
\<close>

locale H = LF + fixes z :: nat assumes hz: "Qc z"
context H begin
lemmas foo2 [case_names a b] = LF.foo
ML \<open>local
(* (i) the bare lemmas: case a lands on A, consumes 1 = K *)
val (info, n) = Rule_Cases.get @{thm foo2};
val _ = \<^assert> (map (#1 o #1) info = ["a", "b"] andalso n = 1);
val _ = \<^assert> (light_copy \<^context> 1 (@{thm foo2}, heavy_foo2));
in end\<close>
declare LF.foo [elim]
ML \<open>
(* (ii) the bare declare: the registered rule's major premise is A, as the twin's *)
val _ = \<^assert> (light_elim \<^context> (claset_rule \<^context> Bires.elim_kind @{thm LF.foo}, heavy_foo_elim));
\<close>
lemmas foo2' [case_names a b] = LF.foo[OF LF_axioms]
ML \<open>local
(* the compensating spelling: the bare copy with its exported premise discharged, K 0 as the twin *)
val _ = \<^assert> (diff_K 0 (@{thm foo2'}, heavy_foo2));
val _ = \<^assert> (Thm.eq_thm_prop (Exported_Premises.discharge [@{thm LF_axioms}] @{thm foo2}, @{thm foo2'}));
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = \<^assert> (cases_text (run ctxt [@{thm LF_axioms}, h] "cases" "W n") = heavy_H_cases);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
in end\<close>
(* the nested layer: H's block reads the record copy after the nested end, made by the standard
   morphism that puts the nested assumption in front (d = 1), so K = 1 + 1; the theory copy
   H.foo3 K 3 (the controls at the end) *)
context assumes hc: "Qc (0::nat)" begin
lemmas foo3 = LF.foo
end
ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm foo3} = 2 andalso Thm.nprems_of @{thm foo3} = 4 andalso
  hd (Thm.prems_of @{thm foo3}) aconv \<^prop>\<open>Qc (0::nat)\<close>);
\<close>
(* two nested layers: between the two ends the outer layer's copy (standard_notes, d = 1), after
   the outer end the record copy (d = 2) *)
context assumes hc1: "Qc (1::nat)" begin
context assumes hc2: "Qc (2::nat)" begin
lemmas foo4 = LF.foo
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm foo4} = 2 andalso Thm.nprems_of @{thm foo4} = 4)\<close>
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm foo4} = 3 andalso Thm.nprems_of @{thm foo4} = 5)\<close>
(* a fixes-only nested layer: the record copy generalises (Thm.generalize clears the tags even
   when w does not occur), d = 0, so K = 1; inside the layer, its own layer's copy, the same *)
context fixes w :: nat begin
lemmas nh4 = LF.foo
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm nh4} = 1 andalso Thm.nprems_of @{thm nh4} = 3)\<close>
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm nh4} = 1 andalso Thm.nprems_of @{thm nh4} = 3)\<close>
end

context H begin
ML \<open>
(* (iii) the block re-opened (the identity morphism): as (i) and (ii) *)
val _ = \<^assert> (light_copy \<^context> 1 (@{thm foo2}, heavy_foo2));
val _ = \<^assert> (light_elim \<^context> (claset_rule \<^context> Bires.elim_kind @{thm LF.foo}, heavy_foo_elim));
\<close>
end

interpretation I: H t 0 by (simp add: H_def H_axioms_def LF_def UP_cring_def t Qc1_ax)
ML \<open>local
(* (iv) the theory copy of foo2 after the interpretation (the registration morphism) against
   the twin's; LF's foo has no interpreted copy (the exported theorem serves every context):
   its theory-level elim registration against the twin's interpreted copy *)
val ctxt = \<^context>;
val _ = \<^assert> (light_copy ctxt 1 (@{thm I.foo2}, @{thm Ih.foo2}));
val _ = \<^assert> (light_elim ctxt
  (claset_rule ctxt Bires.elim_kind @{thm LF.foo}, claset_rule ctxt Bires.elim_kind @{thm Ih.foo}));
in end\<close>
ML \<open>local
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip t n";
val st = run ctxt [@{thm I.LF_axioms}, h] "cases" "W n";
(* the ?case binds say ?P against the twin's ?Pa (D fixes P): up to renaming *)
val _ = \<^assert> (cases_terms (canonical_vars o twin_names ("LF", "D")) st = heavy_interp);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
in end\<close>

(* thm_definition is shared by every named target: a class block, a theory-level anonymous
   block, a heavy importer's header notes clause (its theory copy H2.foo2 carries K 2 since the
   second version) *)
class Cz = fixes zc :: 'a assumes "zc = zc"
context Cz begin
lemmas foo2c [case_names a b] = LF.foo
ML \<open>val _ = \<^assert> (light_copy \<^context> 1 (@{thm foo2c}, heavy_foo2))\<close>
(* h3's row (below) in a class block: the class target shares locale_target_notes (h3c is a
   mechanism fixture, not a user scenario) *)
lemma h3c [THEN conjunct1, exported_premises 1]: "Qc zc \<Longrightarrow> Pc y zc \<and> Pc y zc \<Longrightarrow> Pc y zc \<and> Pc y zc" by assumption
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm h3c} = 1 andalso Thm.nprems_of @{thm h3c} = 2)\<close>
end
context assumes hq: "Qc (1::nat)" begin
lemmas foo2t [case_names a b] = LF.foo
ML \<open>val _ = \<^assert> (light_copy \<^context> 1 (@{thm foo2t}, heavy_foo2))\<close>
end
locale H2 = LF + fixes z :: nat assumes hz: "Qc z" notes foo2 [case_names a b] = LF.foo
context H2 begin
ML \<open>val _ = \<^assert> (light_copy \<^context> 1 (@{thm foo2}, heavy_foo2))\<close>
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H2.foo2} = 2 andalso Thm.nprems_of @{thm H2.foo2} = 4)\<close>

(* the activation morphism of global_interpretation J inside context fixes x assumes hx puts the
   block's assumption in front of every activated fact: K = 1 + 1 (user decision B, 2026-10-18),
   so case a lands on A, and the elim registration H's block made for LF.foo, replayed through J
   into the theory's table, has major premise A; inside the block nothing is added yet, K 1 *)
context fixes x :: nat assumes hx: "Qc x" begin
global_interpretation J: H t x by (simp add: H_def H_axioms_def LF_def UP_cring_def t hx)
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm J.foo2} = 1 andalso Thm.nprems_of @{thm J.foo2} = 3)\<close>
end
ML \<open>local
val th = @{thm J.foo2};
val _ = \<^assert> (Exported_Premises.count_of th = 2 andalso Thm.nprems_of th = 4 andalso
  same_shape (hd (Thm.prems_of th), Logic.varify_global \<^prop>\<open>Qc (x::nat)\<close>));
in end\<close>
ML \<open>local
val (info, n) = Rule_Cases.get @{thm J.foo2};
val _ = \<^assert> (map (#1 o #1) info = ["a", "b"] andalso n = 2);
val _ = \<^assert> (light_copy \<^context> 2 (@{thm J.foo2}, heavy_foo2));
in end\<close>
ML \<open>local
val j_foo = Logic.varify_global \<^prop>\<open>Qc (x::nat) \<Longrightarrow> LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>;
val (key, plain) =
  claset_rule_of Bires.elim_kind (claset_entries_by \<^context> (fn key => same_shape (Thm.prop_of key, j_foo)));
val _ = \<^assert> (Exported_Premises.count_of key = 2 andalso
  same_shape (Thm.major_prem_of plain, Thm.major_prem_of (#2 heavy_foo_elim)));
in end\<close>

(* controls: no heavy theorem carries the K tag *)
ML \<open>
val _ = \<^assert> (not (has_K_tag heavy_foo2) andalso not (has_K_tag (#1 heavy_foo_elim)));
val _ = \<^assert> (not (has_K_tag @{thm Ih.foo2}));
\<close>
(* the theory copies of H's block and of its nested layers keep K: the predicate H ?S ?z in front
   of LF ?S, plus one per nested assumes layer *)
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.foo2} = 2 andalso Thm.nprems_of @{thm H.foo2} = 4)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.foo3} = 3 andalso Thm.nprems_of @{thm H.foo3} = 5)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.foo4} = 4 andalso Thm.nprems_of @{thm H.foo4} = 6)\<close>

(* N5: the class target's theory copy keeps K behind the class predicate: Cz.foo2c is
   class.Cz ?zc ==> LF ?S ==> A ==> B ==> A & B with K 2; Cz.h3c's K came from the lemma line's
   attribute alone, which the class target strips from the theory copy: no K (the control) *)
ML \<open>local
val th = @{thm Cz.foo2c};
val _ = \<^assert> (Exported_Premises.count_of th = 2 andalso Thm.nprems_of th = 4 andalso
  same_shape (hd (Thm.prems_of th), Logic.varify_global \<^prop>\<open>class.Cz (w :: 'w)\<close>));
in end\<close>
ML \<open>val _ = \<^assert> (not (has_K_tag @{thm Cz.h3c}))\<close>

(* N6: the bundle target stores its entries through the theory standard morphism, which renumbers
   J.foo2's index-1 variables (an inference that clears the tags): K comes back as 2 *)
ML \<open>val _ = \<^assert> (Thm.maxidx_of @{thm J.foo2} > 0)\<close>
bundle bJ begin
lemmas yJ = J.foo2
end
ML \<open>
val _ = \<^assert>
  (case bundle_of \<^context> "bJ" of
    [([th], _)] => Exported_Premises.count_of th = 2 andalso Thm.nprems_of th = 4
  | _ => false);
\<close>

(* N8: a nested assumes layer whose assumption is a sort constraint.  The export puts
   PROP SORT_CONSTRAINT('a) in front and the normalisation deletes it again, so the layer adds
   nothing to K; with Qc c beside it the layer adds one.  Each copy its own row: the outer copy
   read in H's block after the nested end, the theory copy after H's end.  declare LF.foo [dest]
   is a mechanism fixture (which premise Classical takes as major), not a user scenario. *)
context H begin
context assumes "SORT_CONSTRAINT('a::type)" begin
lemmas r8 = LF.foo
lemmas r8t = LF.fooT
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm r8} = 1 andalso Thm.nprems_of @{thm r8} = 3)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm r8t} = 1 andalso Thm.nprems_of @{thm r8t} = 1)\<close>
context fixes c :: nat assumes hc8: "Qc c" "SORT_CONSTRAINT('a::type)" begin
lemmas r8m = LF.foo
declare LF.foo [dest]
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm r8m} = 2 andalso Thm.nprems_of @{thm r8m} = 4 andalso
  same_shape (hd (Thm.prems_of @{thm r8m}), Logic.varify_global \<^prop>\<open>Qc (c :: nat)\<close>))\<close>
end
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.r8} = 2 andalso Thm.nprems_of @{thm H.r8} = 4)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.r8t} = 2 andalso Thm.nprems_of @{thm H.r8t} = 2)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm H.r8m} = 3 andalso Thm.nprems_of @{thm H.r8m} = 5)\<close>
(* the dest rule declared in the mixed layer, replayed into the theory's claset through I (LF.foo
   mentions none of H's parameters, so the key keeps LF ?S): Qc ?c ==> LF ?S ==> A ==> B ==> A & B
   carries K 2 (the deleted sort constraint is not
   counted) and the derived rule's major premise is A -- a K 3 would make it B, a K 0 Qc ?c *)
ML \<open>local
val key_shape = Logic.varify_global \<^prop>\<open>Qc (c :: nat) \<Longrightarrow> LF (S :: ('a, 'b) ring_scheme) \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>;
val ctxt = \<^context>;
fun show (key, _, kind) =
  Thm.string_of_thm ctxt key ^ " K " ^ string_of_int (Exported_Premises.count_of key) ^
  (if kind = Bires.dest_kind then " dest" else "");
val with_Qc = claset_entries_by ctxt (exists_Const (fn (c, _) => c = \<^const_name>\<open>Qc\<close>) o Thm.prop_of);
val entries = filter (fn (key, _, _) => same_shape (Thm.prop_of key, key_shape)) with_Qc;
val _ = if null entries then error ("no such key; the keys mentioning Qc:\n" ^ cat_lines (map show with_Qc)) else ();
val (key, plain) = claset_rule_of Bires.dest_kind entries;
val _ = \<^assert> (Exported_Premises.count_of key = 2);
val _ = \<^assert> (same_shape (Thm.prop_of plain, Logic.varify_global
  \<^prop>\<open>A \<Longrightarrow> Qc (c :: nat) \<Longrightarrow> LF (S :: ('a, 'b) ring_scheme) \<Longrightarrow> B \<Longrightarrow> (A \<and> B \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>));
in end\<close>
(* the proof block: the exported fact keeps K 1 *)
notepad
begin
  { assume "SORT_CONSTRAINT('a::type)" note r8p = LF.foo }
  note r8p' = this
  ML_prf \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm r8p'} = 1 andalso Thm.nprems_of @{thm r8p'} = 3)\<close>
end

(* K is checked against the normal form's premises (section 11 (39) M7, (40), (42)): a K-tagged
   input not in HHF form (the light predicate, then a meta-all over own premises: 1 premise, 3
   after Goal.norm_result) keeps K = 1 on the local copy; reachable only from ML, since the export
   morphism of lemmas and declare normalises a result not in HHF form first *)
context H begin
local_setup \<open>fn lthy =>
  let
    val th =
      Thm.forall_intr_vars @{thm conjI}
      |> Thm.implies_intr (Thm.cprop_of @{thm LF_axioms})
      |> Exported_Premises.put 1;
    val _ = \<^assert> (Thm.nprems_of th = 1 andalso Exported_Premises.count_of th = 1 andalso
      not (Drule.is_norm_hhf {protect = false} (Thm.prop_of th)));
  in Local_Theory.notes [((\<^binding>\<open>foo_nhhf\<close>, []), [([th], [])])] lthy |> snd end
\<close>
ML \<open>local
val th = @{thm foo_nhhf};
val _ = \<^assert> (Thm.nprems_of th = 3 andalso hd (Thm.prems_of th) aconv Thm.prop_of @{thm LF_axioms});
val _ = \<^assert> (Exported_Premises.count_of th = 1);
in end\<close>
(* a hand-written K beyond the premise count (made with Thm.tag_rule: reachable from ML only) is
   dropped to 0 on the local copy Local_Theory.note returns, rather than kept as a count that
   makes [elim] raise THM *)
local_setup \<open>fn lthy =>
  let
    val th = Thm.tag_rule (Exported_Premises.exported_premises_tagN, "3") @{thm conjI};
    val ((_, [k3]), lthy') = Local_Theory.note ((\<^binding>\<open>k3\<close>, []), [th]) lthy;
    val _ = \<^assert> (Exported_Premises.count_of k3 = 0 andalso Thm.nprems_of k3 = 2);
  in lthy' end\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm k3} = 0 andalso Thm.nprems_of @{thm k3} = 2)\<close>
(* the attribute normalises to HHF form before tagging (user 2026-10-17): written last on a lemmas
   line whose earlier attributes leave a non-HHF result, the tag survives the export morphism of
   lemmas, which leaves a theorem already in that form alone *)
lemma nh: "Qc z \<Longrightarrow> (\<forall>x. Pc x z \<longrightarrow> Pc x z)" by simp
lemmas nh1 = nh[folded atomize_all atomize_imp, exported_premises 1]
ML \<open>local
val th = @{thm nh1};
val _ = \<^assert> (Thm.nprems_of th = 2 andalso hd (Thm.prems_of th) aconv \<^prop>\<open>Qc z\<close>);
val _ = \<^assert> (Exported_Premises.count_of th = 1);
in end\<close>
(* the range is counted on the normal form: 2 is in range although the raw input has one premise *)
ML \<open>local
val th0 = @{thm nh[folded atomize_all atomize_imp]};
val _ = \<^assert> (Thm.nprems_of th0 = 1 andalso not (Drule.is_norm_hhf {protect = true} (Thm.prop_of th0)));
val th2 = @{thm nh[folded atomize_all atomize_imp, exported_premises 2]};
val _ = \<^assert> (Thm.nprems_of th2 = 2 andalso Exported_Premises.count_of th2 = 2);
in end\<close>
(* on an input not in HHF form the normalisation rebuilds the theorem; the attribute puts the
   input's Rule_Cases tags back (plan line 212): consumes 1 written before it stays the recorded
   value, get_consumes is the larger K; case_names a is kept, also under n = 0 *)
ML \<open>local
val th3 = @{thm nh[folded atomize_all atomize_imp, consumes 1, exported_premises 2]};
val _ = \<^assert> (Thm.nprems_of th3 = 2 andalso Exported_Premises.count_of th3 = 2 andalso
  Exported_Premises.lookup_consumes th3 = SOME 1 andalso Rule_Cases.get_consumes th3 = 2);
in end\<close>
ML \<open>local
val (info, _) = Rule_Cases.get @{thm nh[folded atomize_all atomize_imp, case_names a, exported_premises 1]};
val _ = \<^assert> (map (#1 o #1) info = ["a"]);
in end\<close>
ML \<open>val _ = \<^assert> (Rule_Cases.get_consumes @{thm nh[folded atomize_all atomize_imp, consumes 2, exported_premises 1]} = 2)\<close>
ML \<open>local
val th = @{thm nh[folded atomize_all atomize_imp, case_names a, exported_premises 0]};
val (info, _) = Rule_Cases.get th;
val _ = \<^assert> (map (#1 o #1) info = ["a"] andalso not (has_K_tag th));
in end\<close>
(* the attribute's K on a lemma line survives the record copy (plan row 2): THEN conjunct1 leaves
   variables with index > 0, the record copy's standard morphism renumbers them -- an inference
   that clears the tags -- and K is put back with d = 0; on a lemmas line (h5) the attribute is
   evaluated before the notes, on a result already renumbered: the control (h3 is a mechanism
   fixture, not a user scenario) *)
lemma h0: "Qc z \<Longrightarrow> Pc y z \<and> Pc y z \<Longrightarrow> Pc y z \<and> Pc y z" by assumption
ML \<open>val _ = \<^assert> (Thm.maxidx_of @{thm h0[THEN conjunct1]} > 0)\<close>
lemma h3 [THEN conjunct1, exported_premises 1]: "Qc z \<Longrightarrow> Pc y z \<and> Pc y z \<Longrightarrow> Pc y z \<and> Pc y z" by assumption
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm h3} = 1 andalso Thm.nprems_of @{thm h3} = 2)\<close>
lemmas h5 [THEN conjunct1, exported_premises 1] = h0
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm h5} = 1 andalso Thm.nprems_of @{thm h5} = 2)\<close>
(* the same with a statement-level for clause: the normal form's bound x becomes ?x with index 1,
   renumbered by the record copy (plan line 3224) *)
lemma nh2_raw: "Qc y \<Longrightarrow> (\<forall>x. Pc x y \<longrightarrow> Pc x y)" for y by simp
ML \<open>val _ = \<^assert> (Thm.maxidx_of @{thm nh2_raw[folded atomize_all atomize_imp, exported_premises 1]} > 0)\<close>
lemma nh2 [folded atomize_all atomize_imp, exported_premises 1]: "Qc y \<Longrightarrow> (\<forall>x. Pc x y \<longrightarrow> Pc x y)" for y by simp
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm nh2} = 1 andalso Thm.nprems_of @{thm nh2} = 2)\<close>
end

(* the replay (Locale.add_facts_tagged) of a fact H gained after the registrations: J's activated
   copy of nh1 behind the block assumption, K = 1 + 1; I's with d = 0, K 1 *)
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm J.nh1} = 2 andalso Thm.nprems_of @{thm J.nh1} = 3)\<close>
ML \<open>val _ = \<^assert> (Exported_Premises.count_of @{thm I.nh1} = 1 andalso Thm.nprems_of @{thm I.nh1} = 2)\<close>

(* a theorem re-declared in a light block without hyps is stored as it is, whatever its K (the
   final criterion, re-declaration and no hyps): b = J.foo2 keeps its statement (up to renumbering: the activated
   copy says Qc ?x1, the block's normal form Qc ?x) with K 2; c = I.h3 keeps its statement,
   without LF ?S in front, on the block copy and on the theory copy LF.c alike *)
context LF begin
lemmas b = J.foo2
ML \<open>val _ = \<^assert> (same_shape (Thm.prop_of @{thm b}, Thm.prop_of @{thm J.foo2}) andalso Exported_Premises.count_of @{thm b} = 2)\<close>
lemmas c = I.h3
ML \<open>val _ = \<^assert> (Thm.eq_thm_prop (@{thm c}, @{thm I.h3}) andalso Exported_Premises.count_of @{thm c} = 1)\<close>
end
ML \<open>val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.c}, @{thm I.h3}) andalso Exported_Premises.count_of @{thm LF.c} = 1)\<close>

end
