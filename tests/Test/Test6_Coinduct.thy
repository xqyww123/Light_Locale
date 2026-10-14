(* Plan section 7 test 6, coinduction and coinduct (plan lines 4730-4739), rows in the reopened
   block: with coinductive cp in the block, "using LF_axioms proof (coinduction arbitrary: x rule:
   LF.cp.coinduct)" prints the twin's cases and its invariant has no LF S; unchained it fails with
   the stock method failure; "using LF_axioms h proof (coinduct rule: LF.cp.coinduct)" is the
   regression row, and its instantiated form "coinduct x rule: LF.cp.coinduct" pins the
   own_major_prem branch of the patched main_prop_of; row A: cT [coinduct type: tr0] is stored LF
   ?S first with consumes 1 and K 1, and "using LF_axioms proof (coinduct x z)" prints the twin's
   cases through the instantiated rule, no LF S left; row B: the block codatatype's coinduction
   without a rule (the coinduct type registration attached to the closure) prints the twin's
   cases, no LF S in the invariant.  The twin's rows are bound as ML values in its block.  Section
   11 item (27). *)
theory Test6_Coinduct
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"
typedecl tr0
consts Q0 :: "('a, 'b) ring_scheme \<Rightarrow> tr0 \<Rightarrow> bool"

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
(*no LF premise in any subgoal*)
fun no_LF st = not (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>LF\<close>)) (goal_prems st));
\<close>

context D begin
coinductive cp :: "nat \<Rightarrow> bool" where "cp n \<Longrightarrow> cp (Suc n)" | "Pc S (7::nat) \<Longrightarrow> cp 7"
codatatype str = SCons nat str
lemma cT [coinduct type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> x = (z :: tr0)) \<Longrightarrow> x = z" by simp
end
context D begin
ML \<open>
val heavy =
  let
    val ctxt = fix_in \<^context> [("x", natT)];
    val (h, ctxth) = assume_in \<^context> [("x", natT)] "h" "W x";
    val ctxts = fix_in \<^context> [("s", \<^typ>\<open>str\<close>), ("t", \<^typ>\<open>str\<close>)];
    val ctxty = fix_in \<^context> [("x", \<^typ>\<open>tr0\<close>), ("z", \<^typ>\<open>tr0\<close>)];
  in
    {coinduction = cases_text (run ctxt [] "coinduction arbitrary: x rule: cp.coinduct" "cp x"),
     coinduct = cases_text (run ctxth [h] "coinduct rule: cp.coinduct" "cp x"),
     coinduct_x = cases_text (run ctxth [h] "coinduct x rule: cp.coinduct" "cp x"),
     codatatype = cases_text (run ctxts [] "coinduction arbitrary: s t" "s = t"),
     coinduct_xz = cases_text (run ctxty [] "coinduct x z" "x = z")}
  end;
\<close>
end

context LF begin
coinductive cp :: "nat \<Rightarrow> bool" where "cp n \<Longrightarrow> cp (Suc n)" | "Pc S (7::nat) \<Longrightarrow> cp 7"
codatatype str = SCons nat str
lemma cT [coinduct type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> x = (z :: tr0)) \<Longrightarrow> x = z" by simp
end

context LF begin
ML_val \<open>
val LFa = @{thm LF_axioms};
val ctxt = fix_in \<^context> [("x", natT)];
val st = run ctxt [LFa] "coinduction arbitrary: x rule: LF.cp.coinduct" "LF.cp S x";
val _ = \<^assert> (cases_text st = #coinduction heavy andalso no_LF st);
val _ = \<^assert> ((run ctxt [] "coinduction arbitrary: x rule: LF.cp.coinduct" "LF.cp S x"; false)
  handle ERROR msg => String.isPrefix "Failed to apply initial proof method" (Protocol_Message.clean_output msg));
val (h, ctxth) = assume_in \<^context> [("x", natT)] "h" "W x";
val _ = \<^assert> (cases_text (run ctxth [LFa, h] "coinduct rule: LF.cp.coinduct" "LF.cp S x") = #coinduct heavy);
(* with an instantiation, inst_rule calls main_prop_of: strong_consumes 1 takes the own_major_prem
   branch, not LF ?S *)
val _ = \<^assert> (cases_text (run ctxth [LFa, h] "coinduct x rule: LF.cp.coinduct" "LF.cp S x") = #coinduct_x heavy);
(* row B *)
val ctxts = fix_in \<^context> [("s", \<^typ>\<open>LF.str\<close>), ("t", \<^typ>\<open>LF.str\<close>)];
val st = run ctxts [LFa] "coinduction arbitrary: s t" "s = t";
val _ = \<^assert> (cases_text st = #codatatype heavy andalso no_LF st);
(* row A: the stored form; with the instantiation x z, inst_rule calls main_prop_of, and
   strong_consumes 0 takes the conclusion, not LF ?S *)
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.cT}))
  andalso Exported_Premises.count_of @{thm LF.cT} = 1 andalso Rule_Cases.get_consumes @{thm LF.cT} = 1);
val ctxty = fix_in \<^context> [("x", \<^typ>\<open>tr0\<close>), ("z", \<^typ>\<open>tr0\<close>)];
val st = run ctxty [LFa] "coinduct x z" "x = z";
val _ = \<^assert> (cases_text st = #coinduct_xz heavy andalso no_LF st);
\<close>
end

end
