(* Plan section 7 test 6, the Rule_Cases leaf (plan lines 4432-4463, 4472-4498, 4504-4515,
   4554-4575, and plan lines 4341-4342, 4349 for trS (b) and declare LF.ip.cases; section 11 item (21)).  The same declaration block runs in the heavy twin D and in LF
   (fun f, inductive ip / ev, the mutual evm and odm, fun fm and gm, datatypes tr and tr2, typedef
   T, trS, and a nested block with inductive ip2 and fun f2 and g2).  Every print_cases
   comparison drives "lemma goal using facts proof (method)" through Test_Support's proof_after and
   compares the printed cases and the subgoal count (schematic names canonicalised: D fixes P); the
   twin's rows are bound as ML values in the twin's own blocks.  Declaration block: the local
   copies are found by the named and unnamed forms, chaining LF_axioms there falls to case_split.
   Reopened block: the named and unnamed forms chain LF_axioms first and print the twin's cases;
   the wrong orders fail or fall to case_split; the major premise in the goal; the K = i filter
   rows (i) and (ii), the instantiated forms (ii'), induction, case_tac with the rule, mutual
   induction and Rule_Cases.mutual_rule (the exported premise block exactly), the packages'
   closure found in the Induct tables with the negatives (the block datatype with only h chained
   fails), case_tac/induct_tac on the block datatype, case_product, trS (b), declare LF.ip.cases
   [cases pred: ip], and the nested block with ip2 (K 2, its instantiated form against the
   declaring block's oracle) and f2_g2.  The r9 row lives in the nested-target leaf. *)
theory Test6_Cases
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
(*what a print_cases row records: the printed cases and the number of subgoals*)
fun texts st = (cases_text st, subgoals st);
fun fails ctxt facts method goal = not (can (fn () => run ctxt facts method goal) ());
fun error_prefix p ctxt facts method goal =
  (run ctxt facts method goal; false)
    handle ERROR msg => String.isPrefix p (Protocol_Message.clean_output msg);
fun case_split st = case_names st = ["True", "False"];
fun undefined_case st name =
  (Proof_Context.check_case (Proof.context_of st) true (name, Position.none) []; false)
    handle ERROR msg => String.isPrefix "Undefined case" (Protocol_Message.clean_output msg);
(*the ?case binding of the first case*)
fun first_case_prop st =
  (case Proof_Context.dest_cases NONE (Proof.context_of st) of
    (_, Rule_Cases.Case {binds, ...}) :: _ => the (the (AList.lookup (op =) binds ("case", 0)))
  | _ => raise Fail "no cases");
\<close>

consts Pc :: 'a  Qc :: 'a
axiomatization C :: bool where C_ax: C
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"
typedecl tr0
consts Q0 :: "('a, 'b) ring_scheme \<Rightarrow> tr0 \<Rightarrow> bool"


section \<open>The heavy twin\<close>

context D begin
fun f :: "nat \<Rightarrow> nat" where "f 0 = 0" | "f (Suc n) = f n"
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
inductive evm :: "nat \<Rightarrow> bool" and odm :: "nat \<Rightarrow> bool" where
  "evm 0" | "evm n \<Longrightarrow> odm (Suc n)" | "odm n \<Longrightarrow> evm (Suc n)" | "Pc S (7::nat) \<Longrightarrow> evm 7"
fun fm :: "nat \<Rightarrow> nat" and gm :: "nat \<Rightarrow> nat" where
  "fm 0 = 0" | "fm (Suc n) = gm n" | "gm 0 = 0" | "gm (Suc n) = fm n"
datatype tr = Leaf | Node tr tr
datatype tr2 = Leaf2 | Node2 tr2
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
context fixes y :: nat assumes hy: "Qc y" begin
inductive ip2 :: "nat \<Rightarrow> bool" where z: "ip2 0" | s: "ip2 n \<Longrightarrow> ip2 (Suc n)" | pin: "Pc S y \<Longrightarrow> ip2 7"
fun f2 :: "nat \<Rightarrow> nat" and g2 :: "nat \<Rightarrow> nat" where
  "f2 0 = 0" | "f2 (Suc n) = g2 n" | "g2 0 = 0" | "g2 (Suc n) = f2 n"
ML \<open>
val heavy_decl_nested =
  let val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 n" in
    {ip2_cases = texts (run ctxt [h] "cases" "W n"),
     f2_g2 = texts (run_goals (fix_in \<^context> [("a", natT), ("b", natT)]) []
       "induct a and b rule: f2_g2.induct" ["W a", "V b"])}
  end;
\<close>
end
(* declaration-block rows; the Induct-table oracles are the declaration block's own rules (the
   replayed ones of a reopened block lose their structure, see the dump) *)
ML \<open>
val heavy_decl =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
    val ctxt_t = fix_in \<^context> [("t", \<^typ>\<open>tr\<close>)];
  in
    {ip_cases = texts (run ctxt [h] "cases" "W n"),
     f_induct = texts (run (fix_in \<^context> [("x", natT)]) [] "induct x rule: f.induct" "W x"),
     cases_t = texts (run ctxt_t [] "cases t" "W t"),
     induct_t = texts (run ctxt_t [] "induct t" "W t"),
     ip_cases_rule = @{thm ip.cases}, Abs_T_cases = @{thm Abs_T_cases}, tr_exhaust = @{thm tr.exhaust}}
  end;
\<close>
end

(* the heavy twin's reopened block, nothing chained *)
context D begin
ML \<open>
val heavy =
  let
    val ctxt0 = \<^context>;
    val (h, ctxt) = assume_in ctxt0 [("n", natT)] "h" "ip n";
    val (hev, ctxte) = assume_in ctxt0 [("n", natT)] "h" "ev n";
    val (hf, ctxtf) = assume_in ctxt0 [("n", natT), ("m", natT)] "h" "f n = m";
    val ctxt2 = fix_in ctxt0 [("x", natT), ("y", natT)];
    val ctxt_T = fix_in ctxt0 [("y", \<^typ>\<open>T\<close>)];
    val ctxt_t = fix_in ctxt0 [("t", \<^typ>\<open>tr\<close>)];
    val ctxt_ab = fix_in ctxt0 [("a", \<^typ>\<open>tr\<close>), ("b", \<^typ>\<open>tr2\<close>)];
    val (hq, ctxtq) = assume_in ctxt0 [("t", \<^typ>\<open>tr0\<close>)] "hq" "Q0 S t";
    (* (ii): the twin's bare induct with h chained finds ip's rule *)
    val _ = \<^assert> (case_names (run ctxt [h] "induct" "W n") = ["z", "s"]);
  in
    {f_induct = texts (run (fix_in ctxt0 [("x", natT)]) [] "induct x rule: f.induct" "W x"),
     f_elims = texts (run ctxtf [hf] "cases rule: f.elims" "W n"),
     ip_cases_rule = texts (run ctxt [h] "cases rule: ip.cases" "W n"),
     ip_cases = texts (run ctxt [h] "cases" "W n"),
     ev_induct_apply = texts (run_apply ctxte [] "induct rule: ev.induct" "ev n \<Longrightarrow> W n"),
     ev_induct_n = texts (run ctxte [hev] "induct n" "W n"),
     ev_cases_n = texts (run ctxte [hev] "cases n" "W n"),
     ev_induction = texts (run ctxte [hev] "induction rule: ev.induct" "W n"),
     case_tac_ev = subgoals (run_apply ctxte [] "case_tac n rule: ev.cases" "W n"),
     fm_gm = texts (run_goals ctxt2 [] "induct x and y rule: fm_gm.induct" ["W x", "V y"]),
     evm_odm = texts (run_goals ctxt2 [] "induct x and y rule: evm_odm.inducts"
       ["evm x \<Longrightarrow> W x", "odm y \<Longrightarrow> V y"]),
     (* packages' closure *)
     cases_y = texts (run ctxt_T [] "cases y" "W y"),
     cases_t = texts (run ctxt_t [] "cases t" "W t"),
     induct_t = texts (run ctxt_t [] "induct t" "W t"),
     case_tac_t = subgoals (run_apply ctxt_t [] "case_tac t" "W t"),
     induct_tac_t = subgoals (run_apply ctxt_t [] "induct_tac t" "W t"),
     case_product = texts (run ctxt_ab [] "cases a b rule: tr.exhaust[case_product tr2.exhaust]" "W a b"),
     (* trS (b): the type rule keyed on tr0 is found *)
     trS_cases_t = texts (run ctxtq [hq] "cases t" "W t")}
  end;
\<close>
declare ip.cases [cases pred: ip]
ML \<open>
val heavy_ip_cases_declared =
  let val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n"
  in texts (run ctxt [h] "cases" "W n") end;
\<close>
context fixes y :: nat assumes hy: "Qc y" begin
ML \<open>
(* reopened: the nested layer's abbreviation is gone, ip2 takes y *)
val heavy_nested_ip2_cases =
  let val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 y n" in
    \<^assert> (case_split (run ctxt [h] "cases" "W n"));
    texts (run ctxt [@{thm hy}, h] "cases" "W n")
  end;
\<close>
end
end


section \<open>The light block\<close>

context LF begin
fun f :: "nat \<Rightarrow> nat" where "f 0 = 0" | "f (Suc n) = f n"
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
inductive evm :: "nat \<Rightarrow> bool" and odm :: "nat \<Rightarrow> bool" where
  "evm 0" | "evm n \<Longrightarrow> odm (Suc n)" | "odm n \<Longrightarrow> evm (Suc n)" | "Pc S (7::nat) \<Longrightarrow> evm 7"
fun fm :: "nat \<Rightarrow> nat" and gm :: "nat \<Rightarrow> nat" where
  "fm 0 = 0" | "fm (Suc n) = gm n" | "gm 0 = 0" | "gm (Suc n) = fm n"
datatype tr = Leaf | Node tr tr
datatype tr2 = Leaf2 | Node2 tr2
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
context fixes y :: nat assumes hy: "Qc y" begin
inductive ip2 :: "nat \<Rightarrow> bool" where z: "ip2 0" | s: "ip2 n \<Longrightarrow> ip2 (Suc n)" | pin: "Pc S y \<Longrightarrow> ip2 7"
fun f2 :: "nat \<Rightarrow> nat" and g2 :: "nat \<Rightarrow> nat" where
  "f2 0 = 0" | "f2 (Suc n) = g2 n" | "g2 0 = 0" | "g2 (Suc n) = f2 n"
ML \<open>
(* the instantiated form in the declaring block: ip2's case names and per-case assumption counts,
   the oracle of the reopened block's row (plan lines 4473-4474) *)
val decl_ip2 =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 n";
    val st = run ctxt [h] "cases n" "W n";
  in (case_names st, counts st) end;
\<close>
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 n";
val _ = \<^assert> (texts (run ctxt [h] "cases" "W n") = #ip2_cases heavy_decl_nested);
(* negative: chaining LF_axioms hy in the declaration block falls to case_split, case is undefined *)
val st = run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases" "W n";
val _ = \<^assert> (case_split st andalso undefined_case st "z");
\<close>
end
(* declaration-block rows: the local copies are found, the texts are the heavy block's *)
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
val _ = \<^assert> (texts (run ctxt [h] "cases" "W n") = #ip_cases heavy_decl);
val _ = \<^assert> (texts (run (fix_in \<^context> [("x", natT)]) [] "induct x rule: f.induct" "W x") = #f_induct heavy_decl);
val st = run ctxt [@{thm LF_axioms}, h] "cases" "W n";
val _ = \<^assert> (case_split st andalso undefined_case st "zero");
val ctxt_t = fix_in \<^context> [("t", \<^typ>\<open>tr\<close>)];
val _ = \<^assert> (texts (run ctxt_t [] "cases t" "W t") = #cases_t heavy_decl);
val _ = \<^assert> (texts (run ctxt_t [] "induct t" "W t") = #induct_t heavy_decl);
(* the Induct tables of the declaration block hold the local copies *)
val SOME e1 = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm Abs_T_cases};
val SOME e2 = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>tr\<close> @{thm tr.exhaust};
val SOME e3 = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm ip.cases};
val _ = \<^assert> (three_items (e1, #Abs_T_cases heavy_decl) andalso three_items (e2, #tr_exhaust heavy_decl)
  andalso three_items (e3, #ip_cases_rule heavy_decl));
\<close>
end


section \<open>The reopened light block\<close>

context LF begin
ML_val \<open>
val ctxt0 = \<^context>;
val LFa = @{thm LF_axioms};
val (h, ctxt) = assume_in ctxt0 [("n", natT)] "h" "LF.ip S n";
val (hev, ctxte) = assume_in ctxt0 [("n", natT)] "h" "LF.ev S n";
val (hf, ctxtf) = assume_in ctxt0 [("n", natT), ("m", natT)] "h" "LF.f n = m";

(* named and unnamed, chained LF_axioms first *)
val _ = \<^assert> (texts (run (fix_in ctxt0 [("x", natT)]) [LFa] "induct x rule: LF.f.induct" "W x") = #f_induct heavy);
val _ = \<^assert> (texts (run ctxtf [LFa, hf] "cases rule: LF.f.elims" "W n") = #f_elims heavy);
val _ = \<^assert> (texts (run ctxt [LFa, h] "cases rule: LF.ip.cases" "W n") = #ip_cases_rule heavy);
val _ = \<^assert> (texts (run ctxt [LFa, h] "cases" "W n") = #ip_cases heavy);
(* negatives *)
val _ = \<^assert> (fails ctxtf [hf] "cases rule: LF.f.elims" "W n");
val _ = \<^assert> (fails ctxtf [hf, LFa] "cases rule: LF.f.elims" "W n");
val _ = \<^assert> (case_split (run ctxt [h, LFa] "cases" "W n"));

(* the major premise in the goal *)
val _ = \<^assert> (texts (run_apply ctxte [LFa] "induct rule: LF.ev.induct" "LF.ev S n \<Longrightarrow> W n") = #ev_induct_apply heavy);
val _ = \<^assert> (not (can (fn () => run_apply ctxte [] "induct rule: LF.ev.induct" "LF.ev S n \<Longrightarrow> W n") ()));

(* K = i filter: (i) a K 0 cases rule noted in the proof context is registered and returned first,
   and does not shadow LF.ip.cases *)
val (r0, ctxt_r0) = note_in ctxt "r0" "[case_names Z0 S0, consumes 0, cases pred: ip]" @{thm LF.ip.cases [OF LF_axioms]};
val _ = \<^assert> (Exported_Premises.count_of r0 = 0 andalso #2 (Rule_Cases.get r0) = 0);
val _ = \<^assert> (Thm.eq_thm_prop (hd (Induct.find_casesP ctxt_r0 (Thm.concl_of h)), r0));
val _ = \<^assert> (case_names (run ctxt_r0 [LFa, h] "cases" "W n") = ["z", "s"]);
val (r0i, ctxt_r0i) = note_in ctxt "r0i" "[case_names Z0 S0, consumes 0, induct pred: ip]" @{thm LF.ip.induct [OF LF_axioms]};
val _ = \<^assert> (Exported_Premises.count_of r0i = 0 andalso #2 (Rule_Cases.get r0i) = 0);
val _ = \<^assert> (Thm.eq_thm_prop (hd (Induct.find_inductP ctxt_r0i (Thm.concl_of h)), r0i));
val _ = \<^assert> (case_names (run ctxt_r0i [LFa, h] "induct" "W n") = ["z", "s"]);
(* (ii) the wrong order with a bare induct *)
(* the wrong order does not find ip's rule: as stock with a rule-less first fact, induct falls
   back to the type rules found by a type-variable query (induct.ML:773-778), not to an error *)
val _ = \<^assert> (case_names (run ctxt [h, LFa] "induct" "W n") <> ["z", "s"]);
val _ = \<^assert> (case_names (run ctxt [LFa, h] "induct" "W n") = ["z", "s"]);
(* (ii') instantiated forms *)
val _ = \<^assert> (case_names (run ctxte [hev] "induct n" "W n") = ["0", "Suc"]);
val _ = \<^assert> (case_names (run ctxte [hev] "cases n" "W n") = ["0", "Suc"]);
val _ = \<^assert> (texts (run ctxte [LFa, hev] "induct n" "W n") = #ev_induct_n heavy);
val _ = \<^assert> (texts (run ctxte [LFa, hev] "cases n" "W n") = #ev_cases_n heavy);
val _ = \<^assert> (fails ctxte [LFa, hev] "cases S n" "W n");
val _ = \<^assert> (error_prefix "Rule has fewer variables than instantiations given" ctxte [LFa, hev] "cases S n rule: LF.ev.cases" "W n");
(* induction *)
val _ = \<^assert> (texts (run ctxte [LFa, hev] "induction rule: LF.ev.induct" "W n") = #ev_induction heavy);
(* case_tac with the rule: one subgoal more, LF ?S first, LF.ev ?S n second *)
val st = run_apply ctxte [] "case_tac n rule: LF.ev.cases" "W n";
val _ = \<^assert> (subgoals st = #case_tac_ev heavy + 1);
val _ =
  (case map HOLogic.dest_Trueprop (take 2 (goal_prems st)) of
    [p1, p2] =>
      (case (Term.strip_comb p1, Term.strip_comb p2) of
        ((Const (c1, _), [v as Var _]), (Const (c2, _), [v', n])) =>
          \<^assert> (c1 = \<^const_name>\<open>LF\<close> andalso Long_Name.base_name c2 = "ev" andalso v' aconv v andalso n aconv Free ("n", natT))
      | _ => raise Fail "case_tac shape")
  | _ => raise Fail "case_tac subgoals");
(* mutual induction; the mutual rule's exported premise block is exactly LF ?S, K 1, consumes 1 *)
val ctxt2 = fix_in ctxt0 [("x", natT), ("y", natT)];
val _ = \<^assert> (texts (run_goals ctxt2 [LFa] "induct x and y rule: LF.fm_gm.induct" ["W x", "V y"]) = #fm_gm heavy);
val _ = \<^assert> (texts (run_goals ctxt2 [LFa] "induct x and y rule: LF.evm_odm.inducts"
  ["LF.evm S x \<Longrightarrow> W x", "LF.odm S y \<Longrightarrow> V y"]) = #evm_odm heavy);
val _ = \<^assert> (length @{thms LF.fm_gm.induct} = 2);
val SOME (_, mr) = Rule_Cases.mutual_rule ctxt0 @{thms LF.fm_gm.induct};
val _ = \<^assert> (same_shape (hd (Thm.prems_of mr), Logic.varify_global \<^prop>\<open>LF S\<close>) andalso
  Exported_Premises.count_of mr = 1 andalso Exported_Premises.lookup_consumes mr = SOME 1);
val _ = \<^assert> ((run_goals ctxt2 [] "induct x and y rule: LF.fm_gm.induct" ["W x", "V y"]; false)
  handle ERROR msg => String.isPrefix "Failed to apply initial proof method" (Protocol_Message.clean_output msg));
(* packages' closure: the theory copies are found in the reopened block's tables *)
val ctxt_T = fix_in ctxt0 [("y", \<^typ>\<open>LF.T\<close>)];
val ctxt_t = fix_in ctxt0 [("t", \<^typ>\<open>LF.tr\<close>)];
val SOME e1 = induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases};
val SOME e2 = induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>LF.tr\<close> @{thm LF.tr.exhaust};
val SOME e3 = induct_entry Induct.find_casesP ctxt0 \<^prop>\<open>LF.ip S x\<close> @{thm LF.ip.cases};
val _ = \<^assert> (diff_K 1 (e1, #Abs_T_cases heavy_decl) andalso diff_K 1 (e2, #tr_exhaust heavy_decl)
  andalso diff_K 1 (e3, #ip_cases_rule heavy_decl));
val _ = \<^assert> (texts (run ctxt_T [LFa] "cases y" "W y") = #cases_y heavy);
val _ = \<^assert> (texts (run ctxt_t [LFa] "cases t" "W t") = #cases_t heavy);
val _ = \<^assert> (texts (run ctxt_t [LFa] "induct t" "W t") = #induct_t heavy);
(* negatives *)
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt0 (first_case_prop (run ctxt_t [] "cases t" "W t")));
val _ = \<^assert> (error_prefix "Failed to apply initial proof method" ctxt_t [] "induct t" "W t");
(* plan lines 4480-4483: the block datatype with only h chained -- cases t and induct t fail *)
val ctxt_te = fix_in ctxte [("t", \<^typ>\<open>LF.tr\<close>)];
val _ = \<^assert> (fails ctxt_te [hev] "cases t" "W t" andalso fails ctxt_te [hev] "induct t" "W t");
(* case_tac / induct_tac on the block datatype *)
val st = run_apply ctxt_t [] "case_tac t" "W t";
val _ = \<^assert> (subgoals st = #case_tac_t heavy + 1);
val _ = \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (hd (goal_prems st))) of
    (Const (c, _), [Var _]) => c = \<^const_name>\<open>LF\<close> | _ => false));
val _ = \<^assert> (subgoals (run_apply ctxt_t [] "case_tac t rule: LF.tr.exhaust[OF LF_axioms]" "W t") = #case_tac_t heavy);
val st = run_apply ctxt_t [] "induct_tac t" "W t";
val _ = \<^assert> (subgoals st = #induct_tac_t heavy + 1);
val _ = \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (hd (goal_prems st))) of
    (Const (c, _), [Var _]) => c = \<^const_name>\<open>LF\<close> | _ => false));
val _ = \<^assert> (subgoals (run_apply ctxt_t [] "induct_tac t rule: LF.tr.induct[OF LF_axioms]" "W t") = #induct_tac_t heavy);
(* case_product *)
val ctxt_ab = fix_in ctxt0 [("a", \<^typ>\<open>LF.tr\<close>), ("b", \<^typ>\<open>LF.tr2\<close>)];
val _ = \<^assert> (fails ctxt_ab [] "cases a b rule: LF.tr.exhaust[case_product LF.tr2.exhaust]" "W a b");
val _ = \<^assert> (texts (run ctxt_ab []
  "cases a b rule: LF.tr.exhaust[OF LF_axioms, case_names Leaf Node, case_product LF.tr2.exhaust[OF LF_axioms, case_names Leaf2 Node2]]" "W a b")
  = #case_product heavy);
(* without the case names, the product's cases are numbered *)
val _ = \<^assert> (case_names (run ctxt_ab [] "cases a b rule: LF.tr.exhaust[OF LF_axioms, case_product LF.tr2.exhaust[OF LF_axioms]]" "W a b")
  = ["1_1", "1_2", "2_1", "2_2"]);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.tr.exhaust [OF LF_axioms, case_product LF.tr2.exhaust [OF LF_axioms]]} = 0);
(* trS (b) *)
val _ = \<^assert> (is_some (induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>tr0\<close> @{thm LF.trS}));
val (hq, ctxtq) = assume_in ctxt0 [("t", \<^typ>\<open>tr0\<close>)] "hq" "Q0 S t";
val _ = \<^assert> (texts (run ctxtq [LFa, hq] "cases t" "W t") = #trS_cases_t heavy);
\<close>
declare LF.ip.cases [cases pred: ip]
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = \<^assert> (texts (run ctxt [@{thm LF_axioms}, h] "cases" "W n") = heavy_ip_cases_declared);
\<close>

(* nested: ip2 with K 2 *)
context fixes y :: nat assumes hy: "Qc y" begin
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip2 S y n";
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.ip2.cases} = 2);
val _ = \<^assert> (texts (run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases" "W n") = heavy_nested_ip2_cases);
val _ = \<^assert> (case_split (run ctxt [@{thm LF_axioms}, h] "cases" "W n"));
(* the instantiated form: ip2's case names and per-case assumption counts as in the declaring block *)
val st = run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases n" "W n";
val _ = \<^assert> (case_names st = ["z", "s", "pin"]);
val _ = \<^assert> ((case_names st, counts st) = decl_ip2);
val _ = \<^assert> (texts (run_goals (fix_in \<^context> [("a", natT), ("b", natT)]) [@{thm LF_axioms}, @{thm hy}]
  "induct a and b rule: LF.f2_g2.induct" ["W a", "V b"]) = #f2_g2 heavy_decl_nested);
(* the mutual rule's exported premise block is exactly LF ?S, Qc ?y: K 2, consumes 2 *)
val _ = \<^assert> (length @{thms LF.f2_g2.induct} = 2);
val SOME (_, mr) = Rule_Cases.mutual_rule \<^context> @{thms LF.f2_g2.induct};
val _ = \<^assert> (Exported_Premises.count_of mr = 2 andalso Exported_Premises.lookup_consumes mr = SOME 2 andalso
  same_shape (Logic.mk_conjunction_list (take 2 (Thm.prems_of mr)),
    Logic.varify_global (Logic.mk_conjunction_list [\<^prop>\<open>LF S\<close>, \<^prop>\<open>Qc y\<close>])));
\<close>
end
end

(* mutual_rule on untagged consumes-1 rules: tags as stock *)
inductive pe :: "nat \<Rightarrow> bool" and po :: "nat \<Rightarrow> bool" where "pe 0" | "pe n \<Longrightarrow> po (Suc n)" | "po n \<Longrightarrow> pe (Suc n)"
ML \<open>
val SOME (_, mr) = Rule_Cases.mutual_rule \<^context> @{thms pe_po.inducts};
val _ = \<^assert> (Exported_Premises.lookup_consumes mr = SOME 0 andalso not (has_K_tag mr));
\<close>

end
