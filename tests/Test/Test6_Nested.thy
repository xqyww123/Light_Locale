(* Plan section 7 test 6, the nested-target leaf (plan lines 4370-4386, 4400-4428): inside
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
   bx = refl[of x, keep] in the outer block keeps its loose x.  The print_cases comparison of r9
   belongs to the Rule_Cases leaf. *)
theory Test6_Nested
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_simp = proves (fn c => asm_full_simp_tac c 1);
val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;
fun major_is c th =
  (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of th)) of
    (Const (c', _), args) => c' = c andalso forall is_Var args
  | _ => false);
fun simp_props ctxt = map (Thm.prop_of o #2) (Raw_Simplifier.dest_simps (simpset_of ctxt));
fun mentions c = exists_Const (fn (c', _) => c' = c);
(*the leaf's own table for the block-layer guard group*)
structure Thm_Data6 = Generic_Data (type T = thm list val empty = [] val merge = op @);
fun table ctxt = Thm_Data6.get (Context.Proof ctxt);
fun bundle_of ctxt name = Bundle.get ctxt (Bundle.check ctxt (name, Position.none));
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
ML \<open>val heavy_nested = {fooN = @{thm fooN}, bad' = @{thm bad'}, d = @{thm d}};\<close>
end
ML \<open>val heavy_outer_fooN = @{thm fooN};\<close>
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
    Exported_Premises.count_of key = 2 andalso major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth (Thm.prems_of plain) 1) andalso
    mentions \<^const_name>\<open>Qc\<close> (nth (Thm.prems_of plain) 2))
  (claset_entries (thy_ctxt \<^context>) @{thm LF.bad'}));
\<close>
lemmas r9 [cases pred: Rc] = LF.foo9
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.r9}, @{thm LF.foo9}) andalso Exported_Premises.count_of @{thm LF.r9} = 1);
val _ = \<^assert> (can (fn () => @{thm LF.r9 [OF LF_axioms]}) ());
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
ML_val \<open>
val _ = \<^assert> (plain_equal (@{thm d}, #d heavy_nested));
val _ = \<^assert> (Thm.prop_of @{thm LF.d} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc (y :: 'c) \<Longrightarrow> Qc (x :: 'd) \<Longrightarrow> Pc x\<close>);
val _ = \<^assert> (Thm.nprems_of @{thm LF.d} = 3 andalso Exported_Premises.count_of @{thm LF.d} = 2);
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Qc\<close> plain)
  (claset_entries (thy_ctxt \<^context>) @{thm LF.d}));
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
val _ = \<^assert> (Thm.eq_thm_prop (@{thm fooN}, heavy_outer_fooN));
val _ = \<^assert> (Thm.prop_of @{thm LF.fooN} aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc y \<Longrightarrow> Pc S y\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooN} = 2);
val _ = \<^assert> (by_simp \<^context> \<^prop>\<open>Qc z \<Longrightarrow> Pc S z\<close>);
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>Pc S z\<close>));
(* the outer simpset: fooN's outer copy, with the premise Qc ?y, and not the theory copy *)
val simps = simp_props \<^context>;
val _ = \<^assert> (exists (fn p => mentions \<^const_name>\<open>Pc\<close> p andalso
    length (Logic.strip_imp_prems p) = 1 andalso mentions \<^const_name>\<open>Qc\<close> (hd (Logic.strip_imp_prems p))) simps);
val _ = \<^assert> (not (exists (fn p => mentions \<^const_name>\<open>Pc\<close> p andalso
    exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Logic.strip_imp_prems p)) simps));
\<close>
(* the theory registration of LF.d does not reach the open block; declared here, its major premise is Qc ?x *)
declare LF.d [dest]
ML_val \<open>\<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Qc\<close> plain) (claset_entries \<^context> @{thm LF.d}))\<close>

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
val _ = \<^assert> (not (exists (fn (x, _) => x = "y") (Term.add_frees (Thm.prop_of th3) [])));
val _ = \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (hd (Thm.prems_of th3))) of
    (Const (c, _), [Var _]) => c = \<^const_name>\<open>Qc\<close> | _ => false));
val _ = \<^assert> (Thm.nprems_of th3 = Thm.nprems_of @{thm LF.fooP} + 1 andalso Exported_Premises.count_of th3 = 0);
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

(* reopened: the theory copy LF.fooN is in the simpset with the premises LF ?S, Qc ?y *)
context LF begin
ML_val \<open>
val _ = \<^assert> (exists (fn p => mentions \<^const_name>\<open>Pc\<close> p andalso
    (case Logic.strip_imp_prems p of
      [p1, p2] => Light_Locale_Axiom_Facts.is_light_prop \<^context> p1 andalso mentions \<^const_name>\<open>Qc\<close> p2
    | _ => false)) (simp_props \<^context>));
\<close>
end

end
