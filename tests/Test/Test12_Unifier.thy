(* Plan section 7 test 12 (repair phase, step 1), rule R's two unification attempts and the
   beta-eta normalisation (batch-1 plan section 4.1; master plan lines 5373-5385).  B4 command:
   (i) Lq.uq -- Pattern.match fails, Pattern.unify with the fact on the left binds the fact's type
   variable; (ii) a premise that is no pattern is returned unchanged, with no warning, when no fact
   matches it, and is discharged when a schematic fact matches it (the Pattern.match attempt); (ii')
   Lr.uxy -- the fact's variables are renamed apart before matching; instance_tac on a subgoal
   whose conclusion has a loose Bound; a higher-order binding whose beta redex appears only after
   instantiation.  A13 command: add stores the beta-eta normal form.  Eta command: a premise that
   is not eta normal is discharged, the conclusion is left as it is. *)
theory Test12_Unifier
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale Lq = fixes S :: "'a set" and k :: nat assumes "S = S \<and> k = k"
lemma (in Lq) uq: "(x::'a) = x" by (rule refl)
interpretation Q: Lq T 0 for T :: "'c set" by unfold_locales simp

light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"
lemma (in LFs) u1: "(x::'b) = x" by (rule refl)
interpretation I: LFs "{}::nat set" by (rule LFs.intro) simp

light_locale Lr = fixes S :: "'a set" and k :: nat assumes "S = S \<and> k = k"
lemma (in Lr) uxy: "(x :: 'a \<times> 'b) = x" by (rule refl)
interpretation Q2: Lr T k for T :: "'b set" and k by unfold_locales simp

interpretation I2: LFs "{x::nat. x = 0 \<and> True}" by (rule LFs.intro) simp
lemma hw5: "LFs {x::nat. G x \<and> True} \<Longrightarrow> True" by (rule TrueI)


section \<open>B4 command\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val discharge = Light_Locale_Axiom_Facts.discharge_leading ctxt;
  (*?S := ?F ?y, whence ?'a := nat*)
  val with_Fy =
    Drule.infer_instantiate ctxt
      [(("S", 0), Thm.cterm_of ctxt (Var (("F", 0), \<^typ>\<open>nat \<Rightarrow> nat set\<close>) $ Var (("y", 0), \<^typ>\<open>nat\<close>)))];
  val u1_Fy = with_Fy @{thm LFs.u1};
  fun tvars th = Term.add_tvars (Thm.prop_of th) [];
in
val _ = check_rows
 [("Lq.uq", fn () =>
    let val th = discharge @{thm Lq.uq}
    in Thm.nprems_of th = 0 andalso length (tvars th) = 1 andalso null (Term.add_tfrees (Thm.prop_of th) []) end),
  ("not a pattern", fn () =>
    let val (th, warnings) = with_warnings (fn () => discharge u1_Fy)
    in Thm.eq_thm_strict (th, u1_Fy) andalso null warnings end),
  ("not a pattern, schematic fact", fn () => discharges ctxt 1 (with_Fy @{thm Lr.uxy})),
  ("Lr.uxy", fn () =>
    let val th = discharge @{thm Lr.uxy}
    in Thm.nprems_of th = 0 andalso length (tvars th) = 2 end),
  ("Bound key", fn () =>
    (case Seq.pull (Light_Locale_Axiom_Facts.instance_tac ctxt 1
        (Goal.init \<^cprop>\<open>\<And>x::nat set. Lq x 0\<close>)) of
      SOME (st, _) => Thm.nprems_of st = 0
    | NONE => false)),
  ("beta", fn () => discharges ctxt 1 @{thm hw5})]
end
\<close>


section \<open>A13 command\<close>

light_locale LFf = fixes f :: "nat \<Rightarrow> nat" assumes "f 0 = f 0"
consts c0 :: nat

ML \<open>
local
  val ctxt = \<^context>;
  val lff = Const (\<^const_name>\<open>LFf\<close>, \<^typ>\<open>(nat \<Rightarrow> nat) \<Rightarrow> bool\<close>);
  val eta = Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>plus c0\<close> $ Bound 0);
  val beta_eta = Abs ("g", \<^typ>\<open>nat \<Rightarrow> nat\<close>, Bound 0) $ eta;
  val normal = \<^prop>\<open>LFf (plus c0)\<close>;
  fun fact arg = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (lff $ arg)));
  fun stored arg =
    let val ctxt' = Context.proof_map (Light_Locale_Axiom_Facts.add (fact arg)) ctxt
    in (case Light_Locale_Axiom_Facts.retrieve ctxt' normal of [th] => Thm.prop_of th aconv normal | _ => false) end;
  fun not_normal arg = let val t = Thm.prop_of (fact arg) in not (t aconv Envir.beta_eta_contract t) end;
in
val _ = check_rows
 [("A13 guard", fn () => not_normal eta andalso not_normal beta_eta),
  ("A13 eta", fn () => stored eta),
  ("A13 beta eta", fn () => stored beta_eta)]
end
\<close>


section \<open>Eta command\<close>

interpretation I3: LFf "plus c0" by (rule LFf.intro) (rule refl)

ML \<open>
local
  val ctxt = \<^context>;
  val lff_eta =
    HOLogic.mk_Trueprop (Const (\<^const_name>\<open>LFf\<close>, \<^typ>\<open>(nat \<Rightarrow> nat) \<Rightarrow> bool\<close>) $
      Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>plus c0\<close> $ Bound 0));
  val th = Thm.trivial (Thm.cterm_of ctxt lff_eta);
in
val _ = check_rows
 [("eta", fn () => Thm.prop_of (Light_Locale_Axiom_Facts.discharge_leading ctxt th) aconv lff_eta)]
end
\<close>

end
