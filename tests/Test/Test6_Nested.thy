(* Plan section 7 test 6, the nested-target leaf (plan lines 4373-4389, 4403-4431): inside
   context LF begin, a nested context fixes y assumes hy: "Qc y" begin block.  The lemma rows
   there (fooN [simp], the simp goal, bad' [elim] without warning, d [dest]) and the redeclaration
   rows (r9 [cases pred: Rc] = LF.foo9, declare LF.foo9[elim]) are compared with the heavy twin's
   nested block; after the nested end the outer block sees the stock standard_notes export
   (fooN: Qc ?y ==> Pc S ?y), its simpset holds that copy and not the theory copy LF.fooN, which
   appears only in a reopened block; h2b loses the nested type variable.  The bundle group and the
   block-layer guard group (i)-(viii): a bundle noted in the nested block comes back in the outer
   block without the nested assumption and with K 1 when the outer layer's export does not change
   the theorem (bn, bS), as stock when it does (bn3), a theory fact unchanged (bn2); the leaf's own
   Thm_Data6 table filled by declaration (pervasive) / plain declaration in nested blocks is read
   in the outer block by its head and absolute length, and at theory level after the outer end;
   bx = refl[of x, keep] in the outer block keeps its loose x.  The r9 row, with its print_cases
   comparison, lives here in whole (section 11, item (20)). *)
theory Test6_Nested
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun mentions c = exists_Const (fn (c', _) => c' = c);
(*the leaf's own table for the block-layer guard group*)
structure Thm_Data6 = Generic_Data (type T = thm list val empty = [] val merge = op @);
fun table ctxt = Thm_Data6.get (Context.Proof ctxt);
\<close>

consts Rc :: 'a  Sc :: 'a  Pc :: 'a  Qc :: 'a
consts gq6 :: "nat \<Rightarrow> nat"
axiomatization where
  Sc_ax: "Sc x" and Pc_ax: "Pc x y" and Pc1_ax: "Pc x" and
  gq6_0: "gq6 0 = 1" and gq6_1: "gq6 1 = 2"


section \<open>The heavy twin's nested block\<close>

context D begin
lemma fooP: "Pc x y" by (rule Pc_ax)
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
context fixes y assumes hy: "Qc y" begin
lemma fooN [simp]: "Pc S y" by (rule Pc_ax)
lemma "Pc S y" by (simp add: hy)
local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      theorem_in lthy (Binding.name "bad'") "[elim]" "Rc x S \<Longrightarrow> Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax}));
  in \<^assert> (null w); lthy' end\<close>
lemma d [dest]: "Qc x \<Longrightarrow> Pc x" by (rule Pc1_ax)
lemmas r9 [cases pred: Rc] = foo9
ML \<open>
val heavy_nested = {fooN = @{thm fooN}, bad' = @{thm bad'}, d = @{thm d}};
(* the r9 row's print_cases, on the rule's own conclusion Sc x so that an Rc rule and not the
   case_split fallback decides the cases; the rule closes the goal (positive control) *)
val heavy_r9 =
  let
    val (hr, ctxtr) = assume_in \<^context> [("x", \<^typ>\<open>nat\<close>)] "hr" "Rc x S";
    val st = run ctxtr [hr] "cases" "Sc x";
  in \<^assert> (subgoals st = 0); (cases_text st, subgoals st) end;
\<close>
end
ML \<open>
val heavy_outer_fooN = @{thm fooN};
val heavy_outer_Pc_simps = filter (mentions \<^const_name>\<open>Pc\<close>) (simp_props \<^context>);
val _ = \<^assert> (not (null heavy_outer_Pc_simps));
\<close>
ML_val \<open>
val _ = \<^assert> (by_simp \<^context> \<^prop>\<open>Qc z \<Longrightarrow> Pc S z\<close>);
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>Pc S z\<close>));
\<close>
end


section \<open>The light nested block\<close>

context LF begin
lemma fooP: "Pc x y" by (rule Pc_ax)
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)

context fixes y assumes hy: "Qc y" begin
lemma fooN [simp]: "Pc S y" by (rule Pc_ax)
ML_val \<open>
val _ = \<^assert> (Light_Locale_Axiom_Facts.premise_count \<^context> = 2);
val _ = \<^assert> (Thm.prop_of @{thm fooN} aconv \<^prop>\<open>Pc S y\<close>);
val _ = \<^assert> (plain_equal (@{thm fooN}, #fooN heavy_nested));
\<close>
lemma "Pc S y" by (simp add: hy)
local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      theorem_in lthy (Binding.name "bad'") "[elim]" "Rc x S \<Longrightarrow> Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax}));
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>
val _ = \<^assert> (plain_equal (@{thm bad'}, #bad' heavy_nested));
(* the theory copy's registration: major premise Rc ?x ?S, then LF ?S, then Qc ?y *)
val _ = \<^assert> (exists (fn (key, plain, _) =>
    Exported_Premises.count_of key = 2 andalso
    same_shape (Logic.mk_conjunction_list (Thm.prems_of plain), Logic.varify_global
      (Logic.mk_conjunction_list [\<^prop>\<open>Rc (x :: 'd) S\<close>, \<^prop>\<open>LF S\<close>, \<^prop>\<open>Qc (y :: 'c)\<close>])))
  (claset_entries (thy_ctxt \<^context>) @{thm LF.bad'}));
\<close>
(* r9 (plan lines 4409-4412): the redeclaration in the nested block, and the cases it prints,
   the same as the twin's up to renaming; before r9 the same text falls to case_split (the
   block's own foo9 has K 0 and the theory copy LF.foo9 is not in the open block's table) *)
ML_val \<open>
val (hr, ctxtr) = assume_in \<^context> [("x", \<^typ>\<open>nat\<close>)] "hr" "Rc x S";
val _ = \<^assert> (case_names (run ctxtr [@{thm LF_axioms}, hr] "cases" "Sc x") = ["True", "False"]);
\<close>
lemmas r9 [cases pred: Rc] = LF.foo9
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.r9}, @{thm LF.foo9}) andalso Exported_Premises.count_of @{thm LF.r9} = 1);
val _ = @{thm LF.r9 [OF LF_axioms]};
val (hr, ctxtr) = assume_in \<^context> [("x", \<^typ>\<open>nat\<close>)] "hr" "Rc x S";
val st = run ctxtr [@{thm LF_axioms}, hr] "cases" "Sc x";
val _ = \<^assert> ((cases_text st, subgoals st) = heavy_r9);
\<close>
declare LF.foo9[elim]
ML_val \<open>
(* the derived rule: major premise first, LF ?S second -- in this block and at theory level *)
fun elim_shape ctxt = exists (fn (_, plain, _) =>
    major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop ctxt (nth (Thm.prems_of plain) 1))
  (claset_entries ctxt @{thm LF.foo9});
val _ = \<^assert> (elim_shape \<^context> andalso elim_shape (thy_ctxt \<^context>));
\<close>
lemma d [dest]: "Qc x \<Longrightarrow> Pc x" by (rule Pc1_ax)
ML \<open>
(* the derived dest rule of LF.d, literally: the user premise Qc ?x first, then the exported block
   premises LF ?S and Qc ?y -- a K = 1 export would put the block's Qc ?y first *)
fun d_registered ctxt =
  exists (fn (_, plain, _) => same_shape (Thm.prop_of plain, Logic.varify_global
      \<^prop>\<open>Qc (x :: 'd) \<Longrightarrow> LF S \<Longrightarrow> Qc (y :: 'c) \<Longrightarrow> (Pc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>))
    (claset_entries ctxt @{thm LF.d});
\<close>
ML_val \<open>
val _ = \<^assert> (plain_equal (@{thm d}, #d heavy_nested));
val _ = \<^assert> (Thm.prop_of @{thm LF.d} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc (y :: 'c) \<Longrightarrow> Qc (x :: 'd) \<Longrightarrow> Pc x\<close>);
val _ = \<^assert> (Thm.nprems_of @{thm LF.d} = 3 andalso Exported_Premises.count_of @{thm LF.d} = 2);
val _ = \<^assert> (d_registered (thy_ctxt \<^context>));
(* the theory copies of the nested block's lemmas: the three items of the preface, K 2 *)
val _ = \<^assert> (block_lemma ("LF", "D") 2 (@{thm LF.fooN}, #fooN heavy_nested));
val _ = \<^assert> (block_lemma ("LF", "D") 2 (@{thm LF.bad'}, #bad' heavy_nested));
val _ = \<^assert> (block_lemma ("LF", "D") 2 (@{thm LF.d}, #d heavy_nested));
\<close>
end

(* the outer block after the nested end *)
ML_val \<open>
(* fooN in the outer block: Qc ?y ==> Pc S ?y, S the block's Free *)
val _ = \<^assert>
  (case (map HOLogic.dest_Trueprop (Thm.prems_of @{thm fooN}), Term.strip_comb (HOLogic.dest_Trueprop (Thm.concl_of @{thm fooN}))) of
    ([Const (q, _) $ (v' as Var _)], (Const (c, _), [s, v as Var _])) =>
      q = \<^const_name>\<open>Qc\<close> andalso c = \<^const_name>\<open>Pc\<close> andalso s aconv \<^term>\<open>S\<close> andalso v' aconv v
  | _ => false);
val _ = \<^assert> (plain_equal (@{thm fooN}, heavy_outer_fooN));
val _ = \<^assert> (Thm.prop_of @{thm LF.fooN} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc y \<Longrightarrow> Pc S y\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooN} = 2);
val _ = \<^assert> (by_simp \<^context> \<^prop>\<open>Qc z \<Longrightarrow> Pc S z\<close>);
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>Pc S z\<close>));
(* the outer simpset's Pc rules are the heavy outer block's (fooN's outer copy with the premise
   Qc ?y), and none carries a light premise (the theory copy is not there) *)
val simps = simp_props \<^context>;
val _ = \<^assert> (eq_set (op aconv) (filter (mentions \<^const_name>\<open>Pc\<close>) simps, heavy_outer_Pc_simps));
val _ = \<^assert> (not (exists (fn p => mentions \<^const_name>\<open>Pc\<close> p andalso
    exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Logic.strip_imp_prems p)) simps));
\<close>
(* the theory registration of LF.d does not reach the open block: no LF.d-keyed rule before the
   declare; declared here, the same rule *)
ML_val \<open>\<^assert> (null (claset_entries \<^context> @{thm LF.d}))\<close>
declare LF.d [dest]
ML_val \<open>\<^assert> (d_registered \<^context>)\<close>

(* h2b: the nested type variable 'b does not survive in the outer copy *)
(* 'a and 'b are the block's own (S :: ('a, 'b) ring_scheme), so the nested one is 'e *)
context fixes q :: 'e begin
lemmas h2b = LF.fooP[of _ q]
end
ML_val \<open>\<^assert> (not (exists (fn (a, _) => a = "'e") (Term.add_tfrees (Thm.prop_of @{thm h2b}) [])))\<close>

(* the bundle group (bn, i, ii, iii in one nested block) *)
context fixes y assumes hy: "Qc y" begin
bundle bn = LF.fooP [keep]
bundle bn2 = add.assoc [keep]
bundle bn3 = LF.fooP[of _ y, keep]
bundle bS = LF.fooP[of S, keep]
end
ML_val \<open>
val no_Qc = not o mentions \<^const_name>\<open>Qc\<close> o Thm.prop_of;
val [([th], srcs)] = bundle_of \<^context> "bn";
val _ = \<^assert> (not (null srcs) andalso no_Qc th andalso Exported_Premises.count_of th = 1);
val _ = \<^assert> (Thm.eq_thm_prop (th, @{thm LF.fooP}));
val [([th2], _)] = bundle_of \<^context> "bn2";
val _ = \<^assert> (Thm.eq_thm_prop (th2, @{thm add.assoc}) andalso Thm.get_tags th2 = Thm.get_tags @{thm add.assoc});
val [([th3], _)] = bundle_of \<^context> "bn3";
(* (ii): the nested y generalised, hy on top, as stock: Qc ?ya ==> LF ?S ==> Pc ?ya ?y, no tag *)
val _ = \<^assert> (same_shape (Thm.prop_of th3,
    Logic.varify_global \<^prop>\<open>Qc (ya :: 'c) \<Longrightarrow> LF S \<Longrightarrow> Pc ya (y :: 'd)\<close>) andalso
  Exported_Premises.count_of th3 = 0);
val [([thS], _)] = bundle_of \<^context> "bS";
val _ = \<^assert> (Thm.eq_thm_prop (thS, @{thm LF.fooP [of S]}) andalso no_Qc thS andalso Exported_Premises.count_of thS = 1);
\<close>

(* the block-layer guard group: (iv), (v), (vi), (viii) in their own nested blocks *)
context fixes y assumes hy: "Qc y" begin
declaration (pervasive) \<open>fn phi => Thm_Data6.map (append (Morphism.fact phi [@{thm gq6_0}]))\<close>
end
ML_val \<open>
val t = table \<^context>;
val _ = \<^assert> (length t = 1);
val h = hd t;
val _ = \<^assert> (Thm.eq_thm_prop (h, @{thm gq6_0}) andalso Thm.nprems_of h = 0 andalso null (Thm.hyps_of h)
  andalso Thm.get_tags h = Thm.get_tags @{thm gq6_0});
\<close>
context fixes y assumes hy: "Qc y" begin
declaration (pervasive) \<open>fn phi => Thm_Data6.map (append (Morphism.fact phi [Thm.reflexive @{cterm y}]))\<close>
end
ML_val \<open>
val t = table \<^context>;
val _ = \<^assert> (length t = 2);
val h = hd t;
val _ = \<^assert> (Thm.prop_of h aconv Logic.varify_global \<^prop>\<open>Qc (y :: 'c) \<Longrightarrow> y \<equiv> y\<close>);
val _ = \<^assert> (null (Thm.get_tags h));
\<close>
context fixes y assumes hy: "Qc y" begin
declaration \<open>fn phi => Thm_Data6.map (append (Morphism.fact phi [@{thm gq6_1}]))\<close>
end
ML_val \<open>
val t = table \<^context>;
val _ = \<^assert> (length t = 3);
val h = hd t;
val _ = \<^assert> (Thm.eq_thm_prop (h, @{thm gq6_1}) andalso Thm.nprems_of h = 0 andalso null (Thm.hyps_of h));
\<close>
context assumes hz6: "gq6 2 = 3" begin
declaration (pervasive) \<open>fn phi => Thm_Data6.map (append (Morphism.fact phi [@{thm hz6}]))\<close>
end
ML_val \<open>
val t = table \<^context>;
val _ = \<^assert> (length t = 4);
val h = hd t;
val _ = \<^assert> (Thm.eq_thm_prop (h, @{lemma "gq6 2 = 3 \<Longrightarrow> gq6 2 = 3" by this}));
val _ = \<^assert> (Thm.nprems_of h = 1 andalso null (Thm.hyps_of h));
\<close>

(* (vii) in the outer block: a loose x is left alone by the export *)
bundle bx = refl[of x, keep]

end

(* theory level after the outer end *)
ML \<open>
val tctxt = Proof_Context.init_global \<^theory>;
val [([th], _)] = bundle_of tctxt "LF.bn";
val _ = \<^assert> (not (mentions \<^const_name>\<open>Qc\<close> (Thm.prop_of th)) andalso Exported_Premises.count_of th = 1);
val [([th3], _)] = bundle_of tctxt "LF.bn3";
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop tctxt (hd (Thm.prems_of th3)) andalso
  not (mentions \<^const_name>\<open>Qc\<close> (Thm.prop_of th3)) andalso Exported_Premises.count_of th3 = 1);
val t = table tctxt;
val _ = \<^assert> (exists (fn th => Thm.eq_thm_prop (th, @{thm gq6_0})) t);
val _ = \<^assert> (not (exists (fn th => Thm.prop_of th aconv Thm.prop_of @{thm gq6_1}) t));
val [([bx], _)] = bundle_of tctxt "LF.bx";
val _ = \<^assert> ((case HOLogic.dest_Trueprop (Thm.prop_of bx) of
    Const (\<^const_name>\<open>HOL.eq\<close>, _) $ Free ("x", _) $ Free ("x", _) => true | _ => false));
val _ = \<^assert> (Thm.nprems_of bx = 0 andalso null (Thm.hyps_of bx) andalso Exported_Premises.count_of bx = 0);
\<close>

(* reopened (plan line 4431): the theory copy LF.fooN is in the simpset, a Pc rule whose premises
   are exactly LF ?S, Qc ?y *)
context LF begin
ML_val \<open>
val _ = \<^assert> (exists (fn p => mentions \<^const_name>\<open>Pc\<close> p andalso
    same_shape (Logic.mk_conjunction_list (Logic.strip_imp_prems p),
      Logic.varify_global (Logic.mk_conjunction_list [\<^prop>\<open>LF S\<close>, \<^prop>\<open>Qc (y :: 'c)\<close>])))
  (simp_props \<^context>));
\<close>
end

end
