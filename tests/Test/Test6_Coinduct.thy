(* Plan section 7 test 6, coinduction and coinduct (plan lines 4730-4739), rows in the reopened
   block: with coinductive cp in the block, "using LF_axioms proof (coinduction arbitrary: x rule:
   LF.cp.coinduct)" prints the twin's cases and its invariant has no LF S; unchained it fails;
   "using LF_axioms h proof (coinduct rule: LF.cp.coinduct)" is the regression row; row A: cT
   [coinduct type: tr0] is stored LF ?S first with consumes 1 and K 1, and "using LF_axioms proof
   (coinduct x z)" prints the twin's cases (the instantiation makes inst_rule use main_prop_of);
   row B: the block codatatype's coinduction (with its rule) prints the twin's cases, no LF S in
   the invariant.  Section 11 item (27). *)
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
fun fix_in ctxt fixes =
  #2 (Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes) ctxt);
fun run ctxt facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
val texts = Unsynchronized.ref (Symtab.empty: string list Symtab.table);
fun row name st = texts := Symtab.update (name, cases_text st) (! texts);
fun same (a, b) = Symtab.lookup (! texts) a = Symtab.lookup (! texts) b andalso is_some (Symtab.lookup (! texts) a);
fun no_LF ctxt st = not (exists (fn p => exists_subterm (fn t => t aconv \<^term>\<open>LF S\<close> orelse (case t of Const (c, _) $ _ => c = \<^const_name>\<open>LF\<close> | _ => false)) p) (Thm.prems_of (#goal (Proof.goal st))));
\<close>

context D begin
coinductive cp :: "nat \<Rightarrow> bool" where "cp n \<Longrightarrow> cp (Suc n)" | "Pc S (7::nat) \<Longrightarrow> cp 7"
codatatype str = SCons nat str
lemma cT [coinduct type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> x = (z :: tr0)) \<Longrightarrow> x = z" by simp
end
context D begin
ML_val \<open>
val ctxt = fix_in \<^context> [("x", natT)];
val _ = row "heavy coinduction" (run ctxt [] "coinduction arbitrary: x rule: cp.coinduct" "cp x");
\<close>
ML_val \<open>
val (h, ctxth) = assume_in \<^context> [("x", natT)] "h" "W x";
val _ = row "heavy coinduct" (run ctxth [h] "coinduct rule: cp.coinduct" "cp x");
\<close>
ML_val \<open>
val ctxts = fix_in \<^context> [("s", \<^typ>\<open>str\<close>), ("t", \<^typ>\<open>str\<close>)];
val _ = row "heavy codatatype coinduction" (run ctxts [] "coinduction arbitrary: s t rule: str.coinduct" "s = t");
\<close>
ML_val \<open>
val ctxty = fix_in \<^context> [("x", \<^typ>\<open>tr0\<close>), ("z", \<^typ>\<open>tr0\<close>)];
val _ = row "heavy coinduct y" (run ctxty [] "coinduct x z" "x = z");
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
val _ = row "light coinduction" (run ctxt [LFa] "coinduction arbitrary: x rule: LF.cp.coinduct" "LF.cp S x");
val st = run ctxt [LFa] "coinduction arbitrary: x rule: LF.cp.coinduct" "LF.cp S x";
val _ = \<^assert> (same ("light coinduction", "heavy coinduction"));
val _ = \<^assert> (no_LF ctxt st);
val _ = \<^assert> (not (can (fn () => run ctxt [] "coinduction arbitrary: x rule: LF.cp.coinduct" "LF.cp S x") ()));
val (h, ctxth) = assume_in \<^context> [("x", natT)] "h" "W x";
val _ = row "light coinduct" (run ctxth [LFa, h] "coinduct rule: LF.cp.coinduct" "LF.cp S x");
val _ = \<^assert> (same ("light coinduct", "heavy coinduct"));
val ctxts = fix_in \<^context> [("s", \<^typ>\<open>LF.str\<close>), ("t", \<^typ>\<open>LF.str\<close>)];
val _ = row "light codatatype coinduction" (run ctxts [LFa] "coinduction arbitrary: s t rule: LF.str.coinduct" "s = t");
val st = run ctxts [LFa] "coinduction arbitrary: s t rule: LF.str.coinduct" "s = t";
val _ = \<^assert> (same ("light codatatype coinduction", "heavy codatatype coinduction"));
val _ = \<^assert> (no_LF ctxts st);
(* row A: the instantiation y makes inst_rule use main_prop_of, the own major premise *)
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.cT}))
  andalso Exported_Premises.count_of @{thm LF.cT} = 1 andalso Rule_Cases.get_consumes @{thm LF.cT} = 1);
val ctxty = fix_in \<^context> [("x", \<^typ>\<open>tr0\<close>), ("z", \<^typ>\<open>tr0\<close>)];
val _ = row "light coinduct y" (run ctxty [LFa] "coinduct x z" "x = z");
val _ = \<^assert> (same ("light coinduct y", "heavy coinduct y"));
\<close>
end

end
