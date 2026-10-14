(* Plan section 7 test 6, interpret I: LF T inside a declaration-block proof (plan lines
   4398-4403): after foo [simp] (about S) and inductive ev in the block, a lemma assuming cring T
   interprets I: LF T; "using I.LF_axioms h proof (cases rule: LF.ev.cases)" works, "using h proof
   cases" falls to case_split and case zero is undefined; on the goal Pc T 0 the bare simp does not
   close it -- the block's tables were copied when the block opened and hold only the block copy
   foo, which is about S, and interpret registers neither I.foo nor the theory copy (plan lines
   2886-2887) -- and "simp add: LF.foo[OF I.LF_axioms]" does: the milestone-1 simp rows.  The
   plan-4403 control (bare simp succeeding in the reopened block, where the conditional theory
   copy is in the simpset) is a milestone-3 solver row (plan line 2889), not written here.  The
   heavy twin's bare simp closes the same goal after interpret I: D "UP T" T.  The fixture foo
   mentions S so that a goal about T exists (section 11, item (27)). *)
theory Test6_Interpret_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

context D begin
lemma foo [simp]: "Pc S (y :: nat)" by (rule Pc_ax)
lemma
  fixes T :: "nat ring"
  assumes T: "cring T"
  shows "Pc T (0 :: nat)"
proof -
  interpret I: D "UP T" T by (rule D.intro) (simp_all add: UP_cring_def T)
  show ?thesis by simp
qed
end

context LF begin
lemma foo [simp]: "Pc S (y :: nat)" by (rule Pc_ax)
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
lemma
  fixes T :: "nat ring" and n :: nat
  assumes T: "cring T" and h: "LF.ev T n"
  shows "LF.ev T n"
proof -
  interpret I: LF T by (simp add: LF_def UP_cring_def T)
  ML_prf \<open>
    val ctxt = \<^context>;
    val _ = \<^assert> (can (fn () => run ctxt [@{thm I.LF_axioms}, @{thm h}] "cases rule: LF.ev.cases" "W n") ());
    val st = run ctxt [@{thm h}] "cases" "W n";
    val _ = \<^assert> (case_names st = ["True", "False"]);
    val _ = \<^assert> ((Proof_Context.check_case (Proof.context_of st) true ("zero", Position.none) []; false)
      handle ERROR msg => String.isPrefix "Undefined case" (Protocol_Message.clean_output msg));
    (* the simp rows on the instance *)
    val goal = Syntax.read_prop ctxt "Pc T (0 :: nat)";
    val _ = \<^assert> (not (can (fn () => proof_after {apply = true} ctxt [] "simp" goal) ()));
    val _ = \<^assert> (subgoals (proof_after {apply = true} ctxt [] "simp add: LF.foo[OF I.LF_axioms]" goal) = 0);
  \<close>
  show ?thesis by (rule h)
qed
end

end
