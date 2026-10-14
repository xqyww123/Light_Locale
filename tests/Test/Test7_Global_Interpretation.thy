(* Plan section 7 test 7: global_interpretation written in an anonymous block with an assumption (decision 11, "no premise"; own leaf).  (1) The control: an ordinary interpretation in the block gives I2.LFx_axioms with 0 premises and a hyp, retrieve finds it, and nothing survives the block.  (2) global_interpretation stores finite ?x ==> LFx ?x (1 premise) which still carries [simp, intro!]: safe turns the goal LFx c into finite c, the simpset has an entry named ..I.LFx_axioms, and the predicate-fact table does not hold it (decision 19's filter).  (3) The remedy declare I.LFx_axioms [rule del, simp del]: safe no longer touches the goal (empty result sequence) and the simpset entry is gone. *)
theory Test7_Global_Interpretation
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

light_locale LFx = fixes S :: "nat set" assumes fx: "finite S"
consts c :: "nat set"

ML \<open>
fun has_fact ctxt name = can (Proof_Context.get_thms ctxt) name;
fun simps_named ctxt suffix =
  exists (fn ((n, _), _) => String.isSuffix suffix n) (Raw_Simplifier.dest_simps (simpset_of ctxt));
fun retrieved_eq ctxt prop th =
  exists (fn th' => Thm.eq_thm_prop (th', th)) (Light_Locale_Axiom_Facts.retrieve ctxt prop);
\<close>

(* (1) the control *)
context fixes x :: "nat set" assumes h: "finite x" begin
interpretation I2: LFx x by (rule LFx.intro) (rule h)
ML_val \<open>
val th = @{thm I2.LFx_axioms};
val _ = \<^assert> (Thm.nprems_of th = 0);
val _ = \<^assert> (not (null (Thm.hyps_of th)));
val _ = \<^assert> (retrieved_eq \<^context> \<^prop>\<open>LFx x\<close> th);
\<close>
end

ML \<open>val _ = \<^assert> (not (has_fact (Proof_Context.init_global \<^theory>) "I2.LFx_axioms"))\<close>

(* (2) global_interpretation *)
context fixes x :: "nat set" assumes h: "finite x" begin
global_interpretation I: LFx x by (rule LFx.intro) (rule h)
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val th = @{thm I.LFx_axioms};
val _ = \<^assert> (Thm.nprems_of th = 1);
val _ = \<^assert> (Thm.prop_of th aconv Logic.varify_global \<^prop>\<open>finite x \<Longrightarrow> LFx x\<close>);
(*safe uses the safe intro rule with a premise once, without backtracking: finite c remains*)
val _ =
  (case Seq.pull (safe_tac ctxt (Goal.init (Thm.cterm_of ctxt \<^prop>\<open>LFx c\<close>))) of
    SOME (st, _) => \<^assert> (Thm.prems_of st = [\<^prop>\<open>finite c\<close>])
  | NONE => error "safe did not change the goal");
val _ = \<^assert> (simps_named ctxt "I.LFx_axioms");
val _ = \<^assert> (not (retrieved_eq ctxt (Thm.prop_of th) th));
\<close>

(* (3) the remedy *)
declare I.LFx_axioms [rule del, simp del]

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (is_none (Seq.pull (safe_tac ctxt (Goal.init (Thm.cterm_of ctxt \<^prop>\<open>LFx c\<close>)))));
val _ = \<^assert> (not (simps_named ctxt "I.LFx_axioms"));
\<close>

end
