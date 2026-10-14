(* Plan section 7 test 6, the Rule_Cases leaf (plan lines 4429-4463, 4472-4479, 4484-4498,
   4504-4515, 4554-4572; section 11 item (21)).  The same declaration block runs in the heavy twin
   D and in LF (fun f, inductive ip / ev, the mutual evm and odm, fun fm and gm, datatypes tr and
   tr2, typedef T, foo9, trS, and a nested block with inductive ip2 and fun f2 and g2).  Every
   print_cases comparison drives "lemma goal using facts proof (method)" through Test_Support's
   proof_after and compares the printed cases (schematic names canonicalised: D fixes P).
   Declaration block: the local copies are found by the named and unnamed forms, chaining
   LF_axioms there falls to case_split.  Reopened block: the named and unnamed forms chain
   LF_axioms first and print the twin's cases; the wrong orders fail or fall to case_split; the
   major premise in the goal; the K = i filter rows (i) and (ii), the instantiated forms (ii'),
   induction, case_tac with the rule, mutual induction and Rule_Cases.mutual_rule, the packages'
   closure found in the Induct tables with the negatives, case_tac/induct_tac on the block
   datatype, case_product, trS (b), declare LF.ip.cases [cases pred: ip], and the nested block
   with r9, ip2 (K 2) and f2_g2. *)
theory Test6_Cases
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun plain msg = XML.content_of (YXML.parse_body msg);
val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;
fun fix_in ctxt fixes =
  #2 (Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes) ctxt);
val natT = \<^typ>\<open>nat\<close>;

(*the recorded print_cases texts of both sides, by row name*)
val texts = Unsynchronized.ref (Symtab.empty: (string list * int) Symtab.table);
fun run ctxt facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
fun run_apply ctxt facts method goal = proof_after {apply = true} ctxt facts method (Syntax.read_prop ctxt goal);
fun record name st = texts := Symtab.update (name, (cases_text st, subgoals st)) (! texts);
fun row name ctxt facts method goal = record name (run ctxt facts method goal);
fun row_apply name ctxt facts method goal = record name (run_apply ctxt facts method goal);
fun same (a, b) =
  (case (Symtab.lookup (! texts) a, Symtab.lookup (! texts) b) of
    (SOME x, SOME y) => x = y
  | _ => false);
fun run2 ctxt facts method (g1, g2) =
  let
    val (text, _) = Method.read_closure_input ctxt (Input.string method);
    val state = Proof.theorem NONE (K I) [[(Syntax.read_prop ctxt g1, [])], [(Syntax.read_prop ctxt g2, [])]] ctxt
      |> Proof.using [[(facts, [])]];
  in Seq.the_result "run2" (Proof.proof (SOME (text, Position.no_range)) state) end;
fun row2 name ctxt facts method goals = record name (run2 ctxt facts method goals);
fun fails ctxt facts method goal = not (can (fn () => run ctxt facts method goal) ());
fun error_prefix p ctxt facts method goal =
  (run ctxt facts method goal; false) handle ERROR msg => String.isPrefix p (plain msg);
fun case_split st = case_names st = ["True", "False"];
fun undefined_case st name =
  (Proof_Context.check_case (Proof.context_of st) true (name, Position.none) []; false)
    handle ERROR msg => String.isPrefix "Undefined case" (plain msg);
(*the ?case binding of the first case*)
fun first_case_prop st =
  (case Proof_Context.dest_cases NONE (Proof.context_of st) of
    (_, Rule_Cases.Case {binds, ...}) :: _ => the (the (AList.lookup (op =) binds ("case", 0)))
  | _ => raise Fail "no cases");
(*note r0 [atts] = th in the context*)
fun note_in ctxt name atts th =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ([(_, [th'])], ctxt') =
      Proof_Context.note_thmss "" [((Binding.name name, map (Attrib.attribute_cmd ctxt) (attribs_of thy atts)), [([th], [])])] ctxt;
  in (th', ctxt') end;
\<close>

consts Pc :: 'a  Qc :: 'a  Rc :: 'a  Sc :: 'a
axiomatization C :: bool where C_ax: C
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x" and Sc_ax: "Sc x"
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
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
context fixes y :: nat assumes hy: "Qc y" begin
inductive ip2 :: "nat \<Rightarrow> bool" where z: "ip2 0" | s: "ip2 n \<Longrightarrow> ip2 (Suc n)" | pin: "Pc S y \<Longrightarrow> ip2 7"
fun f2 :: "nat \<Rightarrow> nat" and g2 :: "nat \<Rightarrow> nat" where
  "f2 0 = 0" | "f2 (Suc n) = g2 n" | "g2 0 = 0" | "g2 (Suc n) = f2 n"
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 n";
val _ = row "heavy decl nested ip2 cases" ctxt [h] "cases" "W n";
val _ = row "heavy decl nested ip2 cases n" ctxt [h] "cases n" "W n";
val _ = row2 "heavy nested f2_g2" (fix_in \<^context> [("a", natT), ("b", natT)]) [] "induct a and b rule: f2_g2.induct" ("W a", "V b");
\<close>
end
(* declaration-block rows *)
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
val _ = row "heavy decl ip cases" ctxt [h] "cases" "W n";
val _ = row "heavy decl f.induct" (fix_in \<^context> [("x", natT)]) [] "induct x rule: f.induct" "W x";
val ctxt_t = fix_in \<^context> [("t", \<^typ>\<open>tr\<close>)];
val _ = row "heavy decl cases t" ctxt_t [] "cases t" "W t";
val _ = row "heavy decl induct t" ctxt_t [] "induct t" "W t";
(* the mutual oracles: the declaration block's own rules (the replayed ones of a reopened block
   lose their structure, see the dump) *)
\<close>
ML \<open>
val heavy_decl = {ip_cases = @{thm ip.cases}, Abs_T_cases = @{thm Abs_T_cases}, tr_exhaust = @{thm tr.exhaust},
  ip_inducts = @{thms ip.inducts}};
\<close>
end

(* the heavy twin's reopened block, nothing chained *)
context D begin
ML_val \<open>
val ctxt0 = \<^context>;
val (h, ctxt) = assume_in ctxt0 [("n", natT)] "h" "ip n";
val (hev, ctxte) = assume_in ctxt0 [("n", natT)] "h" "ev n";
val (hf, ctxtf) = assume_in ctxt0 [("n", natT), ("m", natT)] "h" "f n = m";
val _ = row "heavy f.induct" (fix_in ctxt0 [("x", natT)]) [] "induct x rule: f.induct" "W x";
val _ = row "heavy f.elims" ctxtf [hf] "cases rule: f.elims" "W n";
val _ = row "heavy ip.cases" ctxt [h] "cases rule: ip.cases" "W n";
val _ = row "heavy ip cases" ctxt [h] "cases" "W n";
val _ = row_apply "heavy ev.induct apply" ctxte [] "induct rule: ev.induct" "ev n \<Longrightarrow> W n";
val _ = row "heavy induct (ii)" ctxt [h] "induct" "W n";
val _ = row "heavy ev induct n" ctxte [hev] "induct n" "W n";
val _ = row "heavy ev cases n" ctxte [hev] "cases n" "W n";
val _ = row "heavy ev induction" ctxte [hev] "induction rule: ev.induct" "W n";
val _ = row_apply "heavy case_tac ev" ctxte [] "case_tac n rule: ev.cases" "W n";
val ctxt2 = fix_in ctxt0 [("x", natT), ("y", natT)];
val _ = row2 "heavy fm_gm" ctxt2 [] "induct x and y rule: fm_gm.induct" ("W x", "V y");
val _ = row2 "heavy evm_odm" ctxt2 [] "induct x and y rule: evm_odm.inducts" ("evm x \<Longrightarrow> W x", "odm y \<Longrightarrow> V y");
(* packages' closure *)
val ctxt_T = fix_in ctxt0 [("y", \<^typ>\<open>T\<close>)];
val ctxt_t = fix_in ctxt0 [("t", \<^typ>\<open>tr\<close>)];
val _ = row "heavy cases y" ctxt_T [] "cases y" "W y";
val _ = row "heavy cases t" ctxt_t [] "cases t" "W t";
val _ = row "heavy induct t" ctxt_t [] "induct t" "W t";
val _ = row_apply "heavy case_tac t" ctxt_t [] "case_tac t" "W t";
val _ = row_apply "heavy induct_tac t" ctxt_t [] "induct_tac t" "W t";
val ctxt_ab = fix_in ctxt0 [("a", \<^typ>\<open>tr\<close>), ("b", \<^typ>\<open>tr2\<close>)];
val _ = row "heavy case_product" ctxt_ab [] "cases a b rule: tr.exhaust[case_product tr2.exhaust]" "W a b";
(* trS (b): the type rule keyed on tr0 is found *)
val (hq, ctxtq) = assume_in ctxt0 [("t", \<^typ>\<open>tr0\<close>)] "hq" "Q0 S t";
val _ = row "heavy trS cases t" ctxtq [hq] "cases t" "W t";
\<close>
declare ip.cases [cases pred: ip]
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
val _ = row "heavy ip cases declared" ctxt [h] "cases" "W n";
\<close>
context fixes y :: nat assumes hy: "Qc y" begin
lemmas r9 [cases pred: Rc] = foo9
ML_val \<open>
val (hr, ctxtr) = assume_in \<^context> [("x", natT)] "hr" "Rc x S";
val _ = row "heavy r9 cases" ctxtr [hr] "cases" "W x";
\<close>
ML_val \<open>
(* reopened: the nested layer's abbreviation is gone, ip2 takes y *)
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 y n";
val _ = row "heavy nested ip2 cases" ctxt [@{thm hy}, h] "cases" "W n";
val _ = \<^assert> (case_split (run ctxt [h] "cases" "W n"));
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
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
context fixes y :: nat assumes hy: "Qc y" begin
inductive ip2 :: "nat \<Rightarrow> bool" where z: "ip2 0" | s: "ip2 n \<Longrightarrow> ip2 (Suc n)" | pin: "Pc S y \<Longrightarrow> ip2 7"
fun f2 :: "nat \<Rightarrow> nat" and g2 :: "nat \<Rightarrow> nat" where
  "f2 0 = 0" | "f2 (Suc n) = g2 n" | "g2 0 = 0" | "g2 (Suc n) = f2 n"
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip2 n";
val _ = row "light decl nested ip2 cases" ctxt [h] "cases" "W n";
val _ = \<^assert> (same ("light decl nested ip2 cases", "heavy decl nested ip2 cases"));
val _ = row "light decl nested ip2 cases n" ctxt [h] "cases n" "W n";
(* negative: chaining LF_axioms hy in the declaration block falls to case_split, case is undefined *)
val st = run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases" "W n";
val _ = \<^assert> (case_split st andalso undefined_case st "z");
\<close>
end
(* declaration-block rows: the local copies are found, the texts are the heavy block's *)
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
val _ = row "light decl ip cases" ctxt [h] "cases" "W n";
val _ = \<^assert> (same ("light decl ip cases", "heavy decl ip cases"));
val _ = row "light decl f.induct" (fix_in \<^context> [("x", natT)]) [] "induct x rule: f.induct" "W x";
val _ = \<^assert> (same ("light decl f.induct", "heavy decl f.induct"));
val st = run ctxt [@{thm LF_axioms}, h] "cases" "W n";
val _ = \<^assert> (case_split st andalso undefined_case st "zero");
val ctxt_t = fix_in \<^context> [("t", \<^typ>\<open>tr\<close>)];
val _ = row "light decl cases t" ctxt_t [] "cases t" "W t";
val _ = row "light decl induct t" ctxt_t [] "induct t" "W t";
val _ = \<^assert> (same ("light decl cases t", "heavy decl cases t") andalso same ("light decl induct t", "heavy decl induct t"));
(* the Induct tables of the declaration block hold the local copies *)
val SOME e1 = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm Abs_T_cases};
val SOME e2 = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>tr\<close> @{thm tr.exhaust};
val SOME e3 = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm ip.cases};
val _ = \<^assert> (three_items (e1, #Abs_T_cases heavy_decl) andalso three_items (e2, #tr_exhaust heavy_decl)
  andalso three_items (e3, #ip_cases heavy_decl));
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
val _ = row "light f.induct" (fix_in ctxt0 [("x", natT)]) [LFa] "induct x rule: LF.f.induct" "W x";
val _ = \<^assert> (same ("light f.induct", "heavy f.induct"));
val _ = row "light f.elims" ctxtf [LFa, hf] "cases rule: LF.f.elims" "W n";
val _ = \<^assert> (same ("light f.elims", "heavy f.elims"));
val _ = row "light ip.cases" ctxt [LFa, h] "cases rule: LF.ip.cases" "W n";
val _ = \<^assert> (same ("light ip.cases", "heavy ip.cases"));
val _ = row "light ip cases" ctxt [LFa, h] "cases" "W n";
val _ = \<^assert> (same ("light ip cases", "heavy ip cases"));
(* negatives *)
val _ = \<^assert> (fails ctxtf [hf] "cases rule: LF.f.elims" "W n");
val _ = \<^assert> (fails ctxtf [hf, LFa] "cases rule: LF.f.elims" "W n");
val _ = \<^assert> (case_split (run ctxt [h, LFa] "cases" "W n"));

(* the major premise in the goal *)
val _ = row_apply "light ev.induct apply" ctxte [LFa] "induct rule: LF.ev.induct" "LF.ev S n \<Longrightarrow> W n";
val _ = \<^assert> (same ("light ev.induct apply", "heavy ev.induct apply"));
val _ = \<^assert> (not (can (fn () => run_apply ctxte [] "induct rule: LF.ev.induct" "LF.ev S n \<Longrightarrow> W n") ()));

(* K = i filter: (i) a K 0 cases rule noted in the proof context does not shadow LF.ip.cases *)
val (r0, ctxt_r0) = note_in ctxt "r0" "[case_names Z0 S0, consumes 0, cases pred: ip]" @{thm LF.ip.cases [OF LF_axioms]};
val _ = \<^assert> (Exported_Premises.count_of r0 = 0 andalso #2 (Rule_Cases.get r0) = 0);
val _ = \<^assert> (case_names (run ctxt_r0 [LFa, h] "cases" "W n") = ["z", "s"]);
val (r0i, ctxt_r0i) = note_in ctxt "r0i" "[case_names Z0 S0, consumes 0, induct pred: ip]" @{thm LF.ip.induct [OF LF_axioms]};
val _ = \<^assert> (Exported_Premises.count_of r0i = 0 andalso #2 (Rule_Cases.get r0i) = 0);
val _ = \<^assert> (case_names (run ctxt_r0i [LFa, h] "induct" "W n") = ["z", "s"]);
(* (ii) the wrong order with a bare induct *)
(* the wrong order does not find ip's rule: as stock with a rule-less first fact, induct falls
   back to the type rules found by a type-variable query (induct.ML:773-778), not to an error *)
val _ = \<^assert> (case_names (run ctxt [h, LFa] "induct" "W n") <> ["z", "s"]);
val _ = \<^assert> (case_names (run ctxt [LFa, h] "induct" "W n") = ["z", "s"]);
val _ = \<^assert> (is_some (Symtab.lookup (! texts) "heavy induct (ii)"));
(* (ii') instantiated forms *)
val _ = \<^assert> (case_names (run ctxte [hev] "induct n" "W n") = ["0", "Suc"]);
val _ = \<^assert> (case_names (run ctxte [hev] "cases n" "W n") = ["0", "Suc"]);
val _ = row "light ev induct n" ctxte [LFa, hev] "induct n" "W n";
val _ = row "light ev cases n" ctxte [LFa, hev] "cases n" "W n";
val _ = \<^assert> (same ("light ev induct n", "heavy ev induct n") andalso same ("light ev cases n", "heavy ev cases n"));
val _ = \<^assert> (fails ctxte [LFa, hev] "cases S n" "W n");
val _ = \<^assert> (error_prefix "Rule has fewer variables than instantiations given" ctxte [LFa, hev] "cases S n rule: LF.ev.cases" "W n");
(* induction *)
val _ = row "light ev induction" ctxte [LFa, hev] "induction rule: LF.ev.induct" "W n";
val _ = \<^assert> (same ("light ev induction", "heavy ev induction"));
(* case_tac with the rule: one subgoal more, LF ?S first, LF.ev ?S n second *)
val st = run_apply ctxte [] "case_tac n rule: LF.ev.cases" "W n";
val _ = \<^assert> (subgoals st = #2 (the (Symtab.lookup (! texts) "heavy case_tac ev")) + 1);
val _ =
  (case map HOLogic.dest_Trueprop (take 2 (Thm.prems_of (#goal (Proof.goal st)))) of
    [p1, p2] =>
      (case (Term.strip_comb p1, Term.strip_comb p2) of
        ((Const (c1, _), [v as Var _]), (Const (c2, _), [v', n])) =>
          \<^assert> (c1 = \<^const_name>\<open>LF\<close> andalso Long_Name.base_name c2 = "ev" andalso v' aconv v andalso n aconv Free ("n", natT))
      | _ => raise Fail "case_tac shape")
  | _ => raise Fail "case_tac subgoals");
(* mutual induction *)
val ctxt2 = fix_in ctxt0 [("x", natT), ("y", natT)];
val _ = row2 "light fm_gm" ctxt2 [LFa] "induct x and y rule: LF.fm_gm.induct" ("W x", "V y");
val _ = \<^assert> (same ("light fm_gm", "heavy fm_gm"));
val _ = row2 "light evm_odm" ctxt2 [LFa] "induct x and y rule: LF.evm_odm.inducts" ("LF.evm S x \<Longrightarrow> W x", "LF.odm S y \<Longrightarrow> V y");
val _ = \<^assert> (same ("light evm_odm", "heavy evm_odm"));
val _ = \<^assert> (length @{thms LF.fm_gm.induct} = 2);
val mr = Rule_Cases.mutual_rule ctxt0 @{thms LF.fm_gm.induct};
val _ = \<^assert> ((case mr of SOME (_, th) =>
    Light_Locale_Axiom_Facts.is_light_prop ctxt0 (hd (Thm.prems_of th)) andalso
    Exported_Premises.count_of th = 1 andalso Exported_Premises.lookup_consumes th = SOME 1
  | NONE => false));
val _ = \<^assert> ((run2 ctxt2 [] "induct x and y rule: LF.fm_gm.induct" ("W x", "V y"); false)
  handle ERROR msg => String.isPrefix "Failed to apply initial proof method" (plain msg));
(* packages' closure: the theory copies are found in the reopened block's tables *)
val ctxt_T = fix_in ctxt0 [("y", \<^typ>\<open>LF.T\<close>)];
val ctxt_t = fix_in ctxt0 [("t", \<^typ>\<open>LF.tr\<close>)];
val SOME e1 = induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>LF.T\<close> @{thm LF.Abs_T_cases};
val SOME e2 = induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>LF.tr\<close> @{thm LF.tr.exhaust};
val SOME e3 = induct_entry Induct.find_casesP ctxt0 \<^prop>\<open>LF.ip S x\<close> @{thm LF.ip.cases};
val _ = \<^assert> (diff_K (e1, #Abs_T_cases heavy_decl) andalso diff_K (e2, #tr_exhaust heavy_decl) andalso diff_K (e3, #ip_cases heavy_decl));
val _ = row "light cases y" ctxt_T [LFa] "cases y" "W y";
val _ = row "light cases t" ctxt_t [LFa] "cases t" "W t";
val _ = row "light induct t" ctxt_t [LFa] "induct t" "W t";
val _ = \<^assert> (same ("light cases y", "heavy cases y") andalso same ("light cases t", "heavy cases t") andalso same ("light induct t", "heavy induct t"));
(* negatives *)
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt0 (first_case_prop (run ctxt_t [] "cases t" "W t")));
val _ = \<^assert> (error_prefix "Failed to apply initial proof method" ctxt_t [] "induct t" "W t");
(* case_tac / induct_tac on the block datatype *)
val st = run_apply ctxt_t [] "case_tac t" "W t";
val _ = \<^assert> (subgoals st = #2 (the (Symtab.lookup (! texts) "heavy case_tac t")) + 1);
val _ = \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (hd (Thm.prems_of (#goal (Proof.goal st))))) of
    (Const (c, _), [Var _]) => c = \<^const_name>\<open>LF\<close> | _ => false));
val _ = \<^assert> (subgoals (run_apply ctxt_t [] "case_tac t rule: LF.tr.exhaust[OF LF_axioms]" "W t") =
  #2 (the (Symtab.lookup (! texts) "heavy case_tac t")));
val st = run_apply ctxt_t [] "induct_tac t" "W t";
val _ = \<^assert> (subgoals st = #2 (the (Symtab.lookup (! texts) "heavy induct_tac t")) + 1);
val _ = \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (hd (Thm.prems_of (#goal (Proof.goal st))))) of
    (Const (c, _), [Var _]) => c = \<^const_name>\<open>LF\<close> | _ => false));
val _ = \<^assert> (subgoals (run_apply ctxt_t [] "induct_tac t rule: LF.tr.induct[OF LF_axioms]" "W t") =
  #2 (the (Symtab.lookup (! texts) "heavy induct_tac t")));
(* case_product *)
val ctxt_ab = fix_in ctxt0 [("a", \<^typ>\<open>LF.tr\<close>), ("b", \<^typ>\<open>LF.tr2\<close>)];
val _ = \<^assert> (fails ctxt_ab [] "cases a b rule: LF.tr.exhaust[case_product LF.tr2.exhaust]" "W a b");
val _ = row "light case_product" ctxt_ab []
  "cases a b rule: LF.tr.exhaust[OF LF_axioms, case_names Leaf Node, case_product LF.tr2.exhaust[OF LF_axioms, case_names Leaf2 Node2]]" "W a b";
val _ = \<^assert> (same ("light case_product", "heavy case_product"));
val _ = \<^assert> (not (same ("light case_product", "heavy case_product")) orelse
  case_names (run ctxt_ab [] "cases a b rule: LF.tr.exhaust[OF LF_axioms, case_product LF.tr2.exhaust[OF LF_axioms]]" "W a b")
    <> case_names (run ctxt_ab [] "cases a b rule: LF.tr.exhaust[OF LF_axioms, case_names Leaf Node, case_product LF.tr2.exhaust[OF LF_axioms, case_names Leaf2 Node2]]" "W a b"));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.tr.exhaust [OF LF_axioms, case_product LF.tr2.exhaust [OF LF_axioms]]} = 0);
(* trS (b) *)
val _ = \<^assert> (is_some (induct_entry Induct.find_casesT ctxt0 \<^typ>\<open>tr0\<close> @{thm LF.trS}));
val (hq, ctxtq) = assume_in ctxt0 [("t", \<^typ>\<open>tr0\<close>)] "hq" "Q0 S t";
val _ = row "light trS cases t" ctxtq [LFa, hq] "cases t" "W t";
val _ = \<^assert> (same ("light trS cases t", "heavy trS cases t"));
\<close>
declare LF.ip.cases [cases pred: ip]
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = row "light ip cases declared" ctxt [@{thm LF_axioms}, h] "cases" "W n";
val _ = \<^assert> (same ("light ip cases declared", "heavy ip cases declared"));
\<close>

(* nested: r9 and ip2 with K 2 *)
context fixes y :: nat assumes hy: "Qc y" begin
lemmas r9 [cases pred: Rc] = LF.foo9
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.r9}, @{thm LF.foo9}) andalso Exported_Premises.count_of @{thm LF.r9} = 1);
val (hr, ctxtr) = assume_in \<^context> [("x", natT)] "hr" "Rc x S";
val _ = row "light r9 cases" ctxtr [@{thm LF_axioms}, hr] "cases" "W x";
val _ = \<^assert> (same ("light r9 cases", "heavy r9 cases"));
val _ = \<^assert> (can (fn () => @{thm LF.r9 [OF LF_axioms]}) ());
\<close>
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip2 S y n";
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.ip2.cases} = 2);
val _ = row "light nested ip2 cases" ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases" "W n";
val _ = \<^assert> (same ("light nested ip2 cases", "heavy nested ip2 cases"));
val _ = \<^assert> (case_split (run ctxt [@{thm LF_axioms}, h] "cases" "W n"));
(* the instantiated form: ip2's case names and per-case assumption counts as in the declaring block *)
val st = run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases n" "W n";
val _ = \<^assert> (case_names st = ["z", "s", "pin"]);
fun counts st = map (fn (_, Rule_Cases.Case {assumes, ...}) => length (maps #2 assumes)) (Proof_Context.dest_cases NONE (Proof.context_of st));
val _ = \<^assert> (counts st = counts (run ctxt [@{thm LF_axioms}, @{thm hy}, h] "cases n" "W n"));
val _ = row2 "light nested f2_g2" (fix_in \<^context> [("a", natT), ("b", natT)]) [@{thm LF_axioms}, @{thm hy}] "induct a and b rule: LF.f2_g2.induct" ("W a", "V b");
val _ = \<^assert> (same ("light nested f2_g2", "heavy nested f2_g2"));
val SOME (_, mr) = Rule_Cases.mutual_rule \<^context> @{thms LF.f2_g2.induct};
val _ = \<^assert> (Exported_Premises.count_of mr = 2 andalso
  Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of mr)) andalso
  exists_Const (fn (c, _) => c = \<^const_name>\<open>Qc\<close>) (nth (Thm.prems_of mr) 1));
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
