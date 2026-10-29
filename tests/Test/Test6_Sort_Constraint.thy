(* Plan section 7 test 6, top-level SORT_CONSTRAINT premises under the setclass batch
   (ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md sections 3.3-3.3b, 4): they are ignored by K and
   skipped by the setclass tools and by the readers of the leading K premises.  Hand-made
   theorems SORT_CONSTRAINT('a) ==> LFs S ==> Qs ==> C with K written by Setclass.put
   ([setclass n] normalises first, which deletes the sort constraint).  Command T, at theory level
   where the table has no fact: the count of setclass premises, rule R without facts, the rule's
   own premises, major premise and rotation, the consumes defaults, Setclass.discharge and
   Rule_Cases.consume filling the leading K premises, mutual_rule writing K back and keeping the
   leading K premises in front of one consumed premise, the parameter renaming (rename_params),
   Induct.own_vars_of, the same theorem without the sort constraint (today's values), the
   fallback and the normalisation ignoring the sort constraint.  Command B, in contexts with one predicate fact each: rule R
   behind a sort constraint, closing and resolving past a sort-constraint subgoal (one under a
   parameter), and the variable condition ignoring the sort constraint (F4: a type variable that
   occurs only there may be bound; the control has it in another premise). *)
theory Test6_Sort_Constraint
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
consts Qs :: bool  Rs :: bool  Ps :: "'a set \<Rightarrow> nat \<Rightarrow> bool"
light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"
lemma lfs0: "LFs ({} :: nat set)" by (rule LFs.intro) simp

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
fun sc_of T = Const ("Pure.sort_constraint", Term.itselfT T --> propT) $ Logic.mk_type T;
val cSC = \<^cprop>\<open>SORT_CONSTRAINT('a::type)\<close>;
val cLF = \<^cprop>\<open>LFs (S :: 'a set)\<close>;
val cQ = \<^cprop>\<open>Qs\<close>;
val Q = Thm.term_of cQ and LFS = Thm.term_of cLF and scT = Thm.term_of cSC;
(*LFs S ==> Qs ==> Qs, and with SORT_CONSTRAINT('a) in front*)
val plain = Thm.assume cQ |> Thm.implies_intr cQ |> Thm.implies_intr cLF;
val sc = plain |> Thm.implies_intr cSC;
val k1 = Setclass.put 1 sc and k1n = Setclass.put 1 plain;
(*SORT_CONSTRAINT('a) ==> LFs S ==> Qs ==> Qs | Rs*)
val k1b =
  Drule.infer_instantiate' \<^context> [SOME \<^cterm>\<open>Qs\<close>, SOME \<^cterm>\<open>Rs\<close>] @{thm disjI1}
  |> Thm.implies_intr cLF |> Thm.implies_intr cSC |> Setclass.put 1;
val fact = Thm.assume cLF;
(*SORT_CONSTRAINT('a) ==> LFs S ==> (\<And>x::nat. Rs) ==> Rs, K 1*)
val cB = \<^cprop>\<open>\<And>x::nat. Rs\<close>;
val kp = Thm.assume cB |> Thm.forall_elim \<^cterm>\<open>0::nat\<close> |> Thm.implies_intr cB
  |> Thm.implies_intr cLF |> Thm.implies_intr cSC |> Setclass.put 1;
(*SORT_CONSTRAINT('a) ==> LFs ?S ==> Ps ?S ?x ==> True, K 1*)
val kv = @{thm TrueI} |> Thm.implies_intr \<^cprop>\<open>Ps (S :: 'a set) (x :: nat)\<close>
  |> Thm.implies_intr cLF |> Thm.implies_intr cSC
  |> Drule.generalize (Names.empty, Names.make_set ["S", "x"]) |> Setclass.put 1;
\<close>

(* command T *)
ML \<open>
local
  val ctxt = \<^context>;
  fun consumed th = Setclass.lookup_consumes th;
in
val _ = check_rows
 [("count_sc", fn () => Light_Locale_Axiom_Facts.count_setclass_prems ctxt k1 = 1),
  ("no facts unchanged", fn () => unchanged ctxt k1),
  ("own_prems", fn () => Setclass.own_prems k1 = [Q]),
  ("own_major_prem", fn () => Setclass.own_major_prem k1 aconv Q),
  ("put_major_prem_first", fn () =>
     Thm.prop_of (Setclass.put_major_prem_first k1) aconv Logic.list_implies ([Q, scT, LFS], Q)),
  ("get_consumes", fn () => Setclass.get_consumes k1 = 2),
  ("default_consumes", fn () => consumed (Rule_Cases.default_consumes 1 k1) = SOME 3),
  ("consumes attribute", fn () => consumed (attr (Rule_Cases.consumes 1) k1 ctxt) = SOME 3),
  ("discharge", fn () =>
     Thm.prop_of (Setclass.discharge [fact] k1) aconv Logic.list_implies ([scT, Q], Q)),
  ("consume", fn () =>
     (case Seq.list_of (Rule_Cases.consume ctxt [] [fact] (("a", 2), k1)) of
       [(("a", (1, [])), th)] => Thm.prop_of th aconv Logic.list_implies ([scT, Q], Q)
     | _ => false)),
  ("mutual_rule", fn () =>
     (case Rule_Cases.mutual_rule ctxt [k1, k1b] of
       SOME (_, mr) => Setclass.count_of mr = 1 andalso Setclass.get_consumes mr = 2
     | NONE => false)),
  (*one consumed own premise: the premises up to the last of the leading K stay in front*)
  ("mutual_rule consumed", fn () =>
     (case
        Rule_Cases.mutual_rule ctxt (map (fn th => attr (Rule_Cases.consumes 1) th ctxt) [k1, k1b])
      of
       SOME (_, mr) => eq_list (op aconv) (take 2 (Thm.prems_of mr), [scT, LFS])
     | NONE => false)),
  ("rename_params", fn () =>
     (case nth (Thm.prems_of (Rule_Cases.rename_params [["u"]] kp)) 2 of
       Const ("Pure.all", _) $ Abs (u, _, _) => u = "u"
     | _ => false)),
  ("own_vars_of", fn () =>
     map (#1 o #1 o Term.dest_Var) (Induct.own_vars_of kv (nth (Thm.prems_of kv) 2)) = ["x"]),
  ("normalised", fn () =>
     Setclass.own_prems k1n = [Q] andalso Setclass.get_consumes k1n = 1 andalso
     consumed (Rule_Cases.default_consumes 1 k1n) = SOME 2 andalso
     Thm.prop_of (Setclass.put_major_prem_first k1n) aconv Logic.list_implies ([Q, LFS], Q) andalso
     Thm.prop_of (Setclass.discharge [fact] k1n) aconv Logic.mk_implies (Q, Q) andalso
     (case Seq.list_of (Rule_Cases.consume ctxt [] [fact] (("a", 1), k1n)) of
       [(("a", (0, [])), th)] => Thm.prop_of th aconv Logic.mk_implies (Q, Q)
     | _ => false)),
  ("shift_count ignores SC", fn () =>
     Setclass.count_of (Morphism.thm (Morphism.thm_morphism "addsc" (Thm.implies_intr cSC)) k1n) = 1),
  ("norm keeps K", fn () => Setclass.count_of (Raw_Simplifier.norm_hhf_protect ctxt k1) = 1)]
end
\<close>

(* command B *)
ML \<open>
local
  val ctxt_S = Context.proof_map (Light_Locale_Axiom_Facts.add fact) \<^context>;
  val ctxt_0 = Context.proof_map (Light_Locale_Axiom_Facts.add @{thm lfs0}) \<^context>;
  val discharge = Light_Locale_Axiom_Facts.discharge_setclass_prems;
  fun goal t = Goal.init (Thm.cterm_of ctxt_S t);
  fun prems_are ts sts =
    (case sts of [st] => eq_list (op aconv) (Thm.prems_of st, ts) | _ => false);
  val k2 = Setclass.put 2 sc and k2n = Setclass.put 2 plain;
  (*the sort-constraint subgoal under a parameter*)
  val sc_bound = \<^prop>\<open>\<And>x::nat. SORT_CONSTRAINT('a::type)\<close>;
  val st_close =
    Seq.hd (Goal.conjunction_tac 1 (goal (Logic.mk_conjunction (sc_bound, LFS))));
  (*SORT_CONSTRAINT('a) ==> LFs S ==> True*)
  val r_sc = @{thm TrueI} |> Thm.implies_intr cLF |> Thm.implies_intr cSC;
  (*SORT_CONSTRAINT(?'a) ==> LFs (?S :: ?'a set) ==> True*)
  val f4 = r_sc |> Drule.generalize (Names.make1_set "'a", Names.make1_set "S");
  (*SORT_CONSTRAINT(?'a) ==> LFs ?S ==> ?x = ?x ==> True, ?x :: ?'a*)
  val cE = \<^cprop>\<open>(x :: 'a) = x\<close>;
  val f4b = @{thm TrueI} |> Thm.implies_intr cE |> Thm.implies_intr cLF |> Thm.implies_intr cSC
    |> Drule.generalize (Names.make1_set "'a", Names.make_set ["S", "x"]);
in
val _ = check_rows
 [("R skips SC", fn () =>
     let val r = discharge ctxt_S k2 in
       Thm.prop_of r aconv Logic.list_implies ([scT, Q], Q) andalso
       Setclass.count_of r = 1 andalso Setclass.count_of (discharge ctxt_S k2n) = 1
     end),
  ("close skips SC", fn () =>
     prems_are [sc_bound]
       (Seq.list_of (Light_Locale_Axiom_Facts.close_setclass_prems_tac ctxt_S 1 1 st_close))),
  ("resolve skips SC", fn () =>
     prems_are [scT]
       (Seq.list_of
         (Light_Locale_Axiom_Facts.resolve_closing_setclass_prems ctxt_S [r_sc] 1
           (goal \<^prop>\<open>True\<close>)))),
  ("F4 bind", fn () =>
     Thm.prop_of (discharge ctxt_0 f4) aconv Logic.mk_implies (sc_of natT, \<^prop>\<open>True\<close>)),
  ("F4 control", fn () => unchanged ctxt_0 f4b)]
end
\<close>

end
