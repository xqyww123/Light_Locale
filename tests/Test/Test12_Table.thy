(* Plan section 7 test 12 (repair phase, step 1), the leaf without a theory-level registration
   (batch-1 plan section 4.1): the predicate fact table in the block, in lemma (in LF) and in an
   importing block, and add's two conditions (A1, A2, A5, A12); at theory level, where the table
   has no fact, rule R, instance_tac and resolve_closing_setclass_prems change nothing, the
   counts, and resolve_closing_setclass_prems's results equal resolve_tac's (command T); in the
   reopened block rule R on fooP, fooS, fooM and the hand-made rules, instance_tac,
   resolve_closing_setclass_prems closing exactly the leading setclass subgoals,
   discharge_morphism, Main untouched (command B).  The theory-level copies
   are read from the theory's facts (Global_Theory.get_thm), never through a block name. *)
theory Test12_Table
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

consts Pc :: 'a  Qc :: 'a  c :: "nat ring"
axiomatization where Pc_ax: "Pc x y"

context LF begin
lemma fooP: "Pc x y" by (rule Pc_ax)
lemma fooS: "x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub> = x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub>" by (rule refl)
context fixes y assumes hy: "Qc y" begin
lemma fooM: "Pc y y" by (rule Pc_ax)
end
end

lemma hw: "LF S \<Longrightarrow> True" by (rule TrueI)
lemma hw2: "LF S \<Longrightarrow> LF T \<Longrightarrow> True" by (rule TrueI)
lemma hw3: "Qc y \<Longrightarrow> LF S \<Longrightarrow> True" by (rule TrueI)
lemma hw4: "LF S \<Longrightarrow> Pc S \<Longrightarrow> True" by (rule TrueI)

light_locale L2 = LF + assumes l2: "S = S"
light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"


section \<open>The table (A1, A2, A5, A12)\<close>

context LF begin
ML \<open>
check_rows
 [("A1", fn () => retrieves_only \<^context> \<^prop>\<open>LF S\<close> @{thm LF_axioms}),
  (*add refuses a fact with a premise (n1) and a fact that is not about a light predicate (n2)*)
  ("A12 (n1)", fn () =>
    let
      val th = Thm.implies_intr \<^cprop>\<open>Qc (0::nat)\<close> @{thm LF_axioms};
      val ctxt = Context.proof_map (Light_Locale_Axiom_Facts.add th) \<^context>;
    in null (Light_Locale_Axiom_Facts.retrieve ctxt (Thm.prop_of th)) end),
  ("A12 (n2)", fn () =>
    let val ctxt = Context.proof_map (Light_Locale_Axiom_Facts.add @{thm TrueI}) \<^context>
    in null (Light_Locale_Axiom_Facts.retrieve ctxt (Thm.prop_of @{thm TrueI})) end),
  ("A12 control", fn () =>
    let
      val th = Thm.assume \<^cprop>\<open>LF c\<close>;
      val ctxt = Context.proof_map (Light_Locale_Axiom_Facts.add th) \<^context>;
    in retrieves_only ctxt (Thm.prop_of th) th end)]
\<close>
end

lemma (in LF) "True"
  ML_prf \<open>check_rows [("A2", fn () => retrieves_only \<^context> \<^prop>\<open>LF S\<close> @{thm LF_axioms})]\<close>
  by (rule TrueI)

context L2 begin
ML \<open>
check_rows
 [("A5 LF", fn () => retrieves \<^context> \<^prop>\<open>LF S\<close>),
  ("A5 L2", fn () => retrieves \<^context> \<^prop>\<open>L2 S\<close>)]
\<close>
end

section \<open>Tools where the table has no fact (command T)\<close>

ML \<open>
val thy_thm = Global_Theory.get_thm \<^theory>;
fun goal ctxt t = Goal.init (Thm.cterm_of ctxt t);
\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val [fooP, fooM, hw, hw2, hw3] = map thy_thm ["LF.fooP", "LF.fooM", "hw", "hw2", "hw3"];
  val count = Light_Locale_Axiom_Facts.count_setclass_prems ctxt;
  val st = goal ctxt \<^prop>\<open>A \<or> B\<close>;
  val rules = @{thms disjI1 disjI2};
  val stock = Seq.list_of (resolve_tac ctxt rules 1 st);
in
val _ = check_rows
 [("B1 no facts", fn () => unchanged ctxt fooP),
  ("instance_tac no facts", fn () =>
    is_none (Seq.pull (Light_Locale_Axiom_Facts.instance_tac ctxt 1 (goal ctxt \<^prop>\<open>LF S\<close>)))),
  ("resolve_closing_setclass_prems no facts", fn () =>
    is_none (Seq.pull (Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt [hw] 1
      (goal ctxt \<^prop>\<open>True\<close>)))),
  ("fooM K = 1", fn () => Setclass.count_of fooM = 1),
  ("count fooP = 1", fn () => count fooP = 1),
  ("count fooM = 1", fn () => count fooM = 1),
  ("count hw = 1", fn () => count hw = 1),
  ("count conjI = 0", fn () => count @{thm conjI} = 0),
  ("count hw2 = 2", fn () => count hw2 = 2),
  ("count hw3 = 0", fn () => count hw3 = 0),
  ("hw K = 0", fn () => Setclass.count_of hw = 0),
  ("stock guard", fn () => map Thm.prems_of stock = [[\<^prop>\<open>A\<close>], [\<^prop>\<open>B\<close>]]),
  ("same as resolve_tac", fn () =>
    eq_list Thm.eq_thm
      (Seq.list_of (Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt rules 1 st), stock)),
  ("no rules", fn () =>
    is_none (Seq.pull (Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt [] 1 st)))]
end
\<close>


section \<open>Tools in the reopened block (command B)\<close>

context LF begin
ML \<open>
local
  val ctxt = \<^context>;
  val [fooP, fooS, fooM, hw, hw2, hw3, hw4] =
    map thy_thm ["LF.fooP", "LF.fooS", "LF.fooM", "hw", "hw2", "hw3", "hw4"];
  val fooS_S = Drule.infer_instantiate' ctxt [SOME \<^cterm>\<open>S\<close>] fooS;
  (*hand-made: the first premise has no fact (B5'), the second has none (B5'')*)
  val b5' = @{thm TrueI} |> Thm.implies_intr \<^cprop>\<open>LF S\<close> |> Thm.implies_intr \<^cprop>\<open>LFs X\<close>;
  val b5'' = @{thm TrueI} |> Thm.implies_intr \<^cprop>\<open>LFs X\<close> |> Thm.implies_intr \<^cprop>\<open>LF S\<close>;
  val discharge = Light_Locale_Axiom_Facts.discharge_setclass_prems ctxt;
  val instance = Light_Locale_Axiom_Facts.instance_tac ctxt 1;
  val resolve = Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt;
  fun closes tac t =
    (case Seq.pull (tac (goal ctxt t)) of SOME (st, _) => Thm.nprems_of st = 0 | NONE => false);
  fun two_goals t = Seq.hd (Goal.conjunction_tac 1 (goal ctxt t));
  val phi = Light_Locale_Axiom_Facts.discharge_morphism ctxt;
  val main_facts = Facts.dest_static false [] (Global_Theory.facts_of (Thy_Info.get_theory "Main"));
in
val _ = check_rows
 [("B1", fn () => discharges ctxt 1 fooP),
  ("fooS unchanged", fn () => unchanged ctxt fooS),
  ("fooS[of S]", fn () => discharges ctxt 1 fooS_S),
  ("B5", fn () => discharges ctxt 1 fooM),
  ("B5 K = 0", fn () => Setclass.count_of (discharge fooM) = 0),
  ("B5 K from 2", fn () => Setclass.count_of (discharge (Setclass.put 2 b5'')) = 1),
  ("B5'", fn () => unchanged ctxt b5'),
  ("B5''", fn () => discharges ctxt 1 b5''),
  ("hw3 unchanged", fn () => unchanged ctxt hw3),
  ("hw4 unchanged", fn () => unchanged ctxt hw4),
  ("(a1)", fn () => discharges ctxt 2 hw2),
  ("(a2)", fn () => closes (resolve [hw2] 1) \<^prop>\<open>True\<close>),
  ("instance_tac LF S", fn () => closes instance \<^prop>\<open>LF S\<close>),
  ("instance_tac True", fn () => is_none (Seq.pull (instance (goal ctxt \<^prop>\<open>True\<close>)))),
  ("?P", fn () =>
    is_none (Seq.pull (instance (goal ctxt (HOLogic.mk_Trueprop (Var (("P", 0), HOLogic.boolT))))))),
  ("instance_tac under a binder", fn () => closes instance \<^prop>\<open>\<And>x::nat. LF S\<close>),
  ("resolve_closing_setclass_prems hw", fn () =>
    closes (resolve [hw] 1) \<^prop>\<open>True\<close>),
  ("(f)", fn () =>
    map Thm.prems_of (Seq.list_of (resolve [hw] 1 (two_goals \<^prop>\<open>True &&& LF S\<close>))) =
      [[\<^prop>\<open>LF S\<close>]]),
  ("second subgoal", fn () =>
    map Thm.prems_of (Seq.list_of (resolve [hw] 2 (two_goals \<^prop>\<open>LF S &&& True\<close>))) =
      [[\<^prop>\<open>LF S\<close>]]),
  ("discharge_morphism fooP", fn () =>
    Thm.prop_of (Morphism.thm phi fooP) aconv Thm.concl_of fooP),
  ("discharge_morphism fooM", fn () => Setclass.count_of (Morphism.thm phi fooM) = 0),
  ("Main facts", fn () => length (maps #2 main_facts) > 10000),
  ("B6", fn () => forall (fn (_, ths) => forall (unchanged ctxt) ths) main_facts)]
end
\<close>
end

end
