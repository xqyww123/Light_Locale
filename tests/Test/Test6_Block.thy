(* Plan section 7 test 6, the declaration-block leaf (plan lines 4236-4293, 4310-4428, section 11
   item (19)).  The same block text runs in the heavy twin D and in LF: packages (definition, fun,
   inductive with and without intro rules, datatype, typedef, abbreviation, the same-name pair bar),
   bad [elim] with no warning and the goal auto closes, the lemma rows fooP .. fa4 with their tags,
   the failing foo6, the threaded row a/b, the table check right after inductive ip.  The local
   copies are compared with the heavy block facts ("normal equality" or the three items), the
   theory copies LF.x with the heavy block facts (lemma rows: statement, premise count, Rule_Cases
   up to K) or with D.x under phi (package rows).  The attribute-scope rows fa1/fa2 run on the
   fixture pair LFc/DFc (a header assumption fin and a block fact h), fa5 on LM/DM with the new
   variables named in "for"; the bare named form is rejected by stock's global-fact check, a declare
   row with the same loose variables goes through.  Then the reopened blocks: the lemmas and declare
   rows of plan lines 4240-4293 and 4311-4335 against the premise-count oracle D.x and the twin's
   rows, the tag rows h5/h5'/h6/foo7/foo7', fr2/fr', r', trS, foo9/ip.cases/ipc, fa6/fa7, the simp
   row of milestone 1 and the theory-level negatives. *)
theory Test6_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_auto = proves auto_tac;
val by_simp = proves (fn c => simp_tac c 1);
val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;
(*error messages come with markup*)
fun plain msg = XML.content_of (YXML.parse_body msg);
fun facts_of ctxt names = Symtab.make (map (fn n => (n, Proof_Context.get_fact ctxt (Facts.named n))) names);
(*the major premise is the constant c applied to variables only*)
fun major_is c th =
  (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of th)) of
    (Const (c', _), args) => c' = c andalso forall is_Var args
  | _ => false);
val block_names =
  ["fd_def", "f.simps", "ev.intros", "ip.intros", "ip.cases", "ip.inducts", "ipz.cases", "tr.induct",
   "Abs_T_cases", "bar_def", "bad", "fooP", "fooQ", "fooS", "fooT", "fooV", "triv", "triv2", "foo",
   "foo4", "fr", "fr0", "fr0b", "foo9", "r0z", "trS", "aux", "a", "b", "fa3", "fa3b", "fa3c", "fa4"];
\<close>

consts Rc :: 'a  Sc :: 'a  Pc :: 'a  Qc :: 'a  c :: 'a
consts g :: "('a, 'b) ring_scheme \<Rightarrow> nat"  h :: "('a, 'b) ring_scheme \<Rightarrow> nat"
consts gc :: "nat \<Rightarrow> nat"  hc :: "nat \<Rightarrow> nat"
typedecl tz
consts fz :: "('a, 'b) ring_scheme \<Rightarrow> tz"  gz :: "tz \<Rightarrow> tz"  kz :: tz  kc :: tz
typedecl tr0
consts Q0 :: "('a, 'b) ring_scheme \<Rightarrow> tr0 \<Rightarrow> bool"
axiomatization where
  Sc_ax: "Sc x" and Pc_ax: "Pc x y" and Pc1_ax: "Pc x" and Qc_ax: "Qc x y" and Qc1_ax: "Qc x" and Rc1_ax: "Rc x" and
  gc_hc: "gc (hc n) = n" and fz_ax: "fz S = kz" and gz_ax: "gz kz = kc"

(* the theory-level half of the same-name pair *)
definition bar :: "nat \<Rightarrow> nat" where "bar n = n"


section \<open>The heavy twin's block\<close>

context D begin

definition fd :: "nat \<Rightarrow> nat" where "fd n = n + g S"
fun f :: "nat \<Rightarrow> nat" where "f 0 = g S" | "f (Suc n) = f n"
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      Inductive.add_inductive_cmd true false [(Binding.name "ip", SOME "nat \<Rightarrow> bool", NoSyn)] []
        [(((Binding.name "z", []), "ip 0"), [], []),
         (((Binding.name "s", []), "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"), [], [])] [] lthy |> #2);
  in \<^assert> (null w); lthy' end\<close>
inductive ipz :: "nat \<Rightarrow> bool"
datatype tr = Leaf | Node tr tr
lemma "Leaf \<noteq> Node a b" by simp
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
definition bar :: "nat \<Rightarrow> nat" where "bar n = n + g S"
abbreviation cabb where "cabb \<equiv> h S"

local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      theorem_in lthy (Binding.name "bad") "[elim]" "Rc x S \<Longrightarrow> Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax}));
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>\<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>)\<close>

lemma fooP: "Pc x y" by (rule Pc_ax)
lemma fooQ: "Qc x \<Longrightarrow> Pc x y" by (rule Pc_ax)
lemma fooS: "x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub> = x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub>" by (rule refl)
lemma fooT: "Pc S" by (rule Pc1_ax)
lemma fooV: "A \<Longrightarrow> A \<or> B" by (rule disjI1)
lemma triv: "A \<Longrightarrow> B \<Longrightarrow> B" by assumption
lemma triv2 [case_names a b]: "A \<Longrightarrow> B \<Longrightarrow> B" by assumption
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma foo4 [rotated, consumes 1]: "Pc x \<Longrightarrow> Sc y \<Longrightarrow> Qc x y" by (rule Qc_ax)
ML_val \<open>\<^assert> (not (can (fn () =>
  theorem_in \<^context> (Binding.name "foo6") "[consumes 1, rotated]" "Pc x \<Longrightarrow> Sc y \<Longrightarrow> Qc x y"
    (fn ctxt => resolve_tac ctxt @{thms Qc_ax})) ()))\<close>
lemma fr [rule_format, dest]: "\<forall>x. Pc x \<longrightarrow> Qc x" by (simp add: Qc1_ax)
lemma fr0: "\<forall>x. Qc x \<longrightarrow> Pc x" by (simp add: Pc1_ax)
lemma fr0b: "\<forall>x. Qc x S \<longrightarrow> Rc x" by (simp add: Rc1_ax)
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma r0z [consumes 0, cases pred: ip]:
  "ip x \<Longrightarrow> (x = 0 \<Longrightarrow> W) \<Longrightarrow> (\<And>n. x = Suc n \<Longrightarrow> Pc S n \<Longrightarrow> ip n \<Longrightarrow> W) \<Longrightarrow> W"
  by (fact ip.cases)
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
lemma aux [simp]: "gc (hc n) = n" by (rule gc_hc)
lemma "gc (hc 0) = 0" by simp
lemma shows a [simp]: "fz S = kz" and b [simplified]: "gz (fz S) = kc" by (simp_all add: fz_ax gz_ax)
lemma fa3 [unfolded bar_def]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa3b [unfolded D.bar_def]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa3c [unfolded D.bar_def[OF D_axioms]]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa4 [of S]: "Pc x y" by (rule Pc_ax)

ML \<open>val heavy = facts_of \<^context> block_names;\<close>

end


section \<open>The light block\<close>

context LF begin

definition fd :: "nat \<Rightarrow> nat" where "fd n = n + g S"
fun f :: "nat \<Rightarrow> nat" where "f 0 = g S" | "f (Suc n) = f n"
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      Inductive.add_inductive_cmd true false [(Binding.name "ip", SOME "nat \<Rightarrow> bool", NoSyn)] []
        [(((Binding.name "z", []), "ip 0"), [], []),
         (((Binding.name "s", []), "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"), [], [])] [] lthy |> #2);
  in \<^assert> (null w); lthy' end\<close>

(* table check right after inductive ip: the theory copy in the theory's table, the local copy
   in the block's *)
ML_val \<open>
val H = the o Symtab.lookup heavy;
val tctxt = thy_ctxt \<^context>;
val key = \<^prop>\<open>ip x\<close>;
val SOME e = induct_entry Induct.find_casesP tctxt key @{thm LF.ip.cases};
val _ = \<^assert> (diff_K (e, the_single (H "ip.cases")) andalso Exported_Premises.count_of e = 1);
val _ = map2 (fn th => fn hth =>
    let val SOME e = induct_entry Induct.find_inductP tctxt key th
    in \<^assert> (diff_K (e, hth) andalso Exported_Premises.count_of e = 1) end)
  @{thms LF.ip.inducts} (H "ip.inducts");
val SOME e' = induct_entry Induct.find_casesP \<^context> key @{thm ip.cases};
val _ = \<^assert> (three_items (e', the_single (H "ip.cases")));
\<close>

inductive ipz :: "nat \<Rightarrow> bool"
datatype tr = Leaf | Node tr tr
lemma "Leaf \<noteq> Node a b" by simp
typedef T = "{x::nat. x < 5}" by (rule exI[of _ 0]) simp
definition bar :: "nat \<Rightarrow> nat" where "bar n = n + g S"
abbreviation cabb where "cabb \<equiv> h S"

local_setup \<open>fn lthy =>
  let
    val (lthy', w) = with_warnings (fn () =>
      theorem_in lthy (Binding.name "bad") "[elim]" "Rc x S \<Longrightarrow> Sc x" (fn ctxt => resolve_tac ctxt @{thms Sc_ax}));
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>\<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>)\<close>

lemma fooP: "Pc x y" by (rule Pc_ax)
lemma fooQ: "Qc x \<Longrightarrow> Pc x y" by (rule Pc_ax)
lemma fooS: "x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub> = x \<otimes>\<^bsub>UP S\<^esub> \<one>\<^bsub>UP S\<^esub>" by (rule refl)
lemma fooT: "Pc S" by (rule Pc1_ax)
lemma fooV: "A \<Longrightarrow> A \<or> B" by (rule disjI1)
lemma triv: "A \<Longrightarrow> B \<Longrightarrow> B" by assumption
lemma triv2 [case_names a b]: "A \<Longrightarrow> B \<Longrightarrow> B" by assumption
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma foo4 [rotated, consumes 1]: "Pc x \<Longrightarrow> Sc y \<Longrightarrow> Qc x y" by (rule Qc_ax)
ML_val \<open>\<^assert> (not (can (fn () =>
  theorem_in \<^context> (Binding.name "foo6") "[consumes 1, rotated]" "Pc x \<Longrightarrow> Sc y \<Longrightarrow> Qc x y"
    (fn ctxt => resolve_tac ctxt @{thms Qc_ax})) ()))\<close>
lemma fr [rule_format, dest]: "\<forall>x. Pc x \<longrightarrow> Qc x" by (simp add: Qc1_ax)
lemma fr0: "\<forall>x. Qc x \<longrightarrow> Pc x" by (simp add: Pc1_ax)
lemma fr0b: "\<forall>x. Qc x S \<longrightarrow> Rc x" by (simp add: Rc1_ax)
lemma foo9 [cases pred: Rc]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma r0z [consumes 0, cases pred: ip]:
  "ip x \<Longrightarrow> (x = 0 \<Longrightarrow> W) \<Longrightarrow> (\<And>n. x = Suc n \<Longrightarrow> Pc S n \<Longrightarrow> ip n \<Longrightarrow> W) \<Longrightarrow> W"
  by (fact ip.cases)
lemma trS [consumes 1, cases type: tr0]: "Q0 S y \<Longrightarrow> (y = y \<Longrightarrow> W) \<Longrightarrow> W" by simp
lemma aux [simp]: "gc (hc n) = n" by (rule gc_hc)
lemma "gc (hc 0) = 0" by simp
lemma shows a [simp]: "fz S = kz" and b [simplified]: "gz (fz S) = kc" by (simp_all add: fz_ax gz_ax)
lemma fa3 [unfolded bar_def]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa3b [unfolded LF.bar_def]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa3c [unfolded LF.bar_def[OF LF_axioms]]: "bar 1 = 1 + g S" by (simp add: bar_def)
lemma fa4 [of S]: "Pc x y" by (rule Pc_ax)

(* the local copies against the heavy block facts *)
ML_val \<open>
val _ = \<^assert> (Light_Locale_Axiom_Facts.premise_count \<^context> = 1);
val light = facts_of \<^context> block_names;
val H = the o Symtab.lookup heavy and L = the o Symtab.lookup light;
fun check p n = \<^assert> (eq_list p (L n, H n));
val _ = map (check plain_equal)
  ["bad", "fooP", "fooQ", "fooS", "fooT", "fooV", "triv", "triv2", "foo", "foo4", "fr", "fr0", "fr0b", "foo9",
   "trS", "aux", "a", "b", "fa3", "fa3c", "fa4"];
val _ = map (check three_items)
  ["fd_def", "f.simps", "ev.intros", "ip.intros", "ip.cases", "ip.inducts", "ipz.cases", "tr.induct",
   "Abs_T_cases", "bar_def", "r0z", "fa3b"];

(* the same-name pair: the block's bar_def unfolds, LF.bar_def is conditional and does not *)
val no_bar = not o exists_Const (fn (c, _) => Long_Name.base_name c = "bar") o Thm.prop_of;
val _ = \<^assert> (no_bar @{thm fa3} andalso not (no_bar @{thm fa3b}) andalso no_bar @{thm fa3c});

(* the threaded row: (1) above; (5) the block simpset lists a's rule and not b's *)
val simps = map (Thm.prop_of o #2) (Raw_Simplifier.dest_simps (simpset_of \<^context>));
val _ = \<^assert> (exists (fn p => #1 (Logic.dest_equals (Logic.strip_imp_concl p)) aconv \<^term>\<open>fz S\<close>) simps);
val _ = \<^assert> (not (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>gz\<close>)) simps));

(* fr: the derived dest rule's major premise is Pc ?x in the block *)
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Pc\<close> plain) (claset_entries \<^context> @{thm fr}));
\<close>

end

(* the theory copies against the heavy block facts (lemma rows) and D.x under phi (package rows) *)
ML \<open>
val H = the o Symtab.lookup heavy;
val LFp = \<^const_name>\<open>LF\<close> and Dp = \<^const_name>\<open>D\<close>;
fun theory_copy n = Proof_Context.get_fact \<^context> (Facts.named ("LF." ^ n));
fun heavy_copy n = Proof_Context.get_fact \<^context> (Facts.named ("D." ^ n));
val _ = map (fn n => \<^assert> (eq_list (block_lemma ("LF", "D") 1) (theory_copy n, H n)))
  ["bad", "fooP", "fooQ", "fooS", "fooT", "fooV", "triv", "triv2", "foo", "foo4", "fr", "fr0", "fr0b", "foo9",
   "r0z", "trS", "aux", "a", "b", "fa3", "fa3b", "fa3c", "fa4"];
val _ = map (fn n =>
    (\<^assert> (eq_list (phi_equal (LFp, Dp)) (theory_copy n, heavy_copy n));
     \<^assert> (eq_list diff_K (theory_copy n, H n))))
  ["fd_def", "f.simps", "ev.intros", "ip.intros", "ip.cases", "ip.inducts", "ipz.cases", "tr.induct",
   "Abs_T_cases", "bar_def"];

(* pinned shapes *)
val _ = \<^assert> (Thm.prop_of @{thm LF.fooP} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc x y\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooQ} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc x \<Longrightarrow> Pc x y\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooT} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc S\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooV} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> A \<or> B\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.triv} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B\<close>
  andalso Exported_Premises.count_of @{thm LF.triv} = 1 andalso Thm.nprems_of @{thm LF.triv} = 3);
val _ = \<^assert> (Thm.prop_of @{thm LF.triv2} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B\<close>
  andalso Exported_Premises.count_of @{thm LF.triv2} = 1
  andalso Rule_Cases.get @{thm LF.triv2} = ([(("a", []), []), (("b", []), [])], 1));
val _ = \<^assert> (Thm.prop_of @{thm LF.foo} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
  andalso Exported_Premises.count_of @{thm LF.foo} = 1
  andalso Rule_Cases.get @{thm LF.foo} = ([(("a", []), []), (("b", []), [])], 2));
val _ = \<^assert> (Thm.prop_of @{thm LF.foo4} aconv
    Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Sc (y :: 'd) \<Longrightarrow> Pc (x :: 'c) \<Longrightarrow> Qc x y\<close>
  andalso Exported_Premises.count_of @{thm LF.foo4} = 1 andalso #2 (Rule_Cases.get @{thm LF.foo4}) = 2);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fr} = 1);
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Pc\<close> plain) (claset_entries \<^context> @{thm LF.fr}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.b} = 1 andalso Thm.nprems_of @{thm LF.b} = 1
  andalso Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.b}))
  andalso Thm.concl_of @{thm LF.b} aconv \<^prop>\<open>gz kz = kc\<close>);
val simps = map (Thm.prop_of o #2) (Raw_Simplifier.dest_simps (simpset_of \<^context>));
(* the simplifier renumbers the rule's variables (LF ?S1 ==> fz ?S1 == kz): structural check *)
val _ = \<^assert> (exists (fn p =>
    (case Logic.dest_equals (Logic.strip_imp_concl p) of
      (Const (c, _) $ Var _, Const (k, _)) => c = \<^const_name>\<open>fz\<close> andalso k = \<^const_name>\<open>kz\<close>
    | _ => false) andalso
    length (Logic.strip_imp_prems p) = 1 andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Logic.strip_imp_prems p))) simps);
val _ = \<^assert> (not (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>gz\<close>)) simps));
(* the predicate premise of LF.bad is the first *)
val _ = \<^assert> (Thm.prop_of @{thm LF.bad} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Sc x\<close>);
(* the theory-level claset: the derived elim rule of LF.bad has major premise Rc ?x ?S, LF ?S second *)
val _ = \<^assert> (exists (fn (_, plain, _) =>
    major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth (Thm.prems_of plain) 1))
  (claset_entries \<^context> @{thm LF.bad}));
\<close>


section \<open>The attribute-scope rows on the other fixtures\<close>

locale DFc = fixes S :: "nat set" assumes fin: "finite S"
begin
lemma h: "finite S" by (rule fin)
lemma fa1 [OF fin]: "finite S \<Longrightarrow> card S = card S" by (rule refl)
lemma fa2 [OF h]: "finite S \<Longrightarrow> finite S \<or> A" by (rule disjI1)
ML \<open>val heavy_c = facts_of \<^context> ["fa1", "fa2"];\<close>
end

light_locale LFc = fixes S :: "nat set" assumes fin: "finite S"
begin
lemma h: "finite S" by (rule fin)
lemma fa1 [OF fin]: "finite S \<Longrightarrow> card S = card S" by (rule refl)
lemma fa2 [OF h]: "finite S \<Longrightarrow> finite S \<or> A" by (rule disjI1)
ML_val \<open>
val _ = \<^assert> (Light_Locale_Axiom_Facts.premise_count \<^context> = 1);
val _ = \<^assert> (plain_equal (@{thm fa1}, the_single (the (Symtab.lookup heavy_c "fa1"))));
val _ = \<^assert> (plain_equal (@{thm fa2}, the_single (the (Symtab.lookup heavy_c "fa2"))));
\<close>
end

ML \<open>
val _ = \<^assert> (block_lemma ("LFc", "DFc") 1 (@{thm LFc.fa1}, the_single (the (Symtab.lookup heavy_c "fa1"))));
val _ = \<^assert> (block_lemma ("LFc", "DFc") 1 (@{thm LFc.fa2}, the_single (the (Symtab.lookup heavy_c "fa2"))));
val _ = \<^assert> (Thm.prop_of @{thm LFc.fa1} aconv Logic.varify_global \<^prop>\<open>LFc S \<Longrightarrow> card S = card S\<close>);
\<close>

(* fa5 (bare index position): the new variables of the instantiation are named in "for", as at
   the theory level and in lemmas rows; the bare named form is rejected by stock's global-fact
   check, a declare row with the same loose variables goes through (section 11, item (19)) *)
context DM begin
lemma fa5 [where x = "a \<otimes> b" for a b]: "x = x" by (rule refl)
lemma hbase: "Pc x" by (rule Pc1_ax)
ML \<open>val heavy_m = @{thm fa5};\<close>
ML_val \<open>\<^assert> ((lemmas_in \<^context> "fa5y" "hbase" "[where x = \"a \<otimes> b\"]"; false)
  handle ERROR msg => String.isPrefix "Malformed global fact" (plain msg))\<close>
declare hbase[where x = "a \<otimes> b", simp]
end

context LM begin
lemma fa5 [where x = "a \<otimes> b" for a b]: "x = x" by (rule refl)
ML_val \<open>\<^assert> (plain_equal (@{thm fa5}, heavy_m))\<close>
ML_val \<open>\<^assert> ((theorem_in \<^context> (Binding.name "fa5b") "[where x = \"a \<otimes> b\"]" "x = x"
    (fn ctxt => resolve_tac ctxt @{thms refl}); false)
  handle ERROR msg =>
    String.isPrefix "Malformed global fact" (plain msg) andalso
    String.isSubstring "Illegal fixed variable: \"a\"" (plain msg))\<close>
lemma hbase: "Pc x" by (rule Pc1_ax)
declare hbase[where x = "a \<otimes> b", simp]
end

ML \<open>
val _ = \<^assert> (block_lemma ("LM", "DM") 1 (@{thm LM.fa5}, heavy_m));
val _ = \<^assert> (Thm.prop_of @{thm LM.fa5} aconv
  Logic.varify_global \<^prop>\<open>LM G \<Longrightarrow> a \<otimes>\<^bsub>G\<^esub> b = a \<otimes>\<^bsub>G\<^esub> b\<close>);
(* the declare row's rule, with the free variable a, is in the theory simpset under LM ?G *)
val _ = \<^assert> (exists (fn p =>
    exists_Const (fn (c, _) => c = \<^const_name>\<open>Pc\<close>) p andalso
    exists (fn (x, _) => x = "a") (Term.add_frees p []) andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Logic.strip_imp_prems p)))
  (map (Thm.prop_of o #2) (Raw_Simplifier.dest_simps (simpset_of \<^context>))));
\<close>


section \<open>The reopened blocks: lemmas and declare rows\<close>

light_locale LF2 = LF + fixes R :: "('c, 'd) ring_scheme" (structure) assumes lf2: "Qc R"
locale D2 = D + fixes R :: "('c, 'd) ring_scheme" (structure) assumes lf2: "Qc R"

lemma (in LF2) fooR: "Pc R x" by (rule Pc_ax)
lemma (in D2) fooR: "Pc R x" by (rule Pc_ax)

(* the heavy twin's reopened block: the premise-count oracles and the twins of the lemmas rows *)
context D begin
lemmas h = D.fooP[of _ c]
context fixes q :: "('c, 'd) ring_scheme" begin
lemmas h2 = D.fooP[of q c]
end
lemmas hz = D.fooP[of _ "c :: 'z"]
lemmas h4 = D.fooP[of _ "\<one>\<^bsub>UP S\<^esub>"]
lemmas hS0 = D.fooS[of _ "\<one>\<^bsub>UP S\<^esub>"]
lemmas hS1 = D.fooS[OF D_axioms, of "\<one>\<^bsub>UP S\<^esub>"]
context fixes q :: "nat \<Rightarrow> 'a" begin
lemmas hS = D.fooS[of _ q]
end
lemmas cj = conjI
lemmas hm = monoid.r_one
lemmas h5 [case_names a b] = foo
declare foo [cases pred: Rc]
lemmas foo7 [consumes 1] = foo
lemmas r' [cases type: T] = Abs_T_cases
declare foo9 [cases pred: Rc]
declare ip.cases [cases pred: ip]
lemmas ipc [case_names Z S, consumes 1] = ip.cases
ML \<open>
val heavy2 = facts_of \<^context> ["h", "h2", "hz", "h4", "hS0", "hS1", "hS", "cj", "hm", "h5", "foo7", "r'", "ipc"];
val heavy2_foo_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm foo});
val heavy2_foo9_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm foo9});
val heavy2_ipcases_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm ip.cases});
val heavy2_r'_entry = the (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm r'});
\<close>
end

context D2 begin
lemmas hp = D.fooP
end

context LF begin

(* declare LF.bad[rotated, elim]: LF.bad is stored unchanged, the rotated instance is registered
   with K 0, its major premise Rc ?x ?S and LF ?S second, and the goal closes *)
declare LF.bad[rotated, elim]
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.bad} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Sc x\<close>);
val rot = @{thm LF.bad [rotated]};
val _ = \<^assert> (Thm.prop_of rot aconv Logic.varify_global \<^prop>\<open>Rc x S \<Longrightarrow> LF S \<Longrightarrow> Sc x\<close>);
val _ = \<^assert> (Exported_Premises.count_of rot = 0);
val _ = \<^assert> (exists (fn (key, plain, _) =>
    Exported_Premises.count_of key = 0 andalso major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth (Thm.prems_of plain) 1))
  (claset_entries \<^context> rot));
val _ = \<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>);
\<close>

lemmas h = LF.fooP[of _ c]
context fixes q :: "('c, 'd) ring_scheme" begin
lemmas h2 = LF.fooP[of q c]
end
ML_val \<open>
(* h2 in the outer block after the nested end: no Free q, instantiable *)
val _ = \<^assert> (not (exists (fn (x, _) => x = "q") (Term.add_frees (Thm.prop_of @{thm h2}) [])));
val _ = \<^assert> (can (fn () => @{thm h2 [of S]}) ());
(* the type variable of q named 'd clashes with LF.fooP's ?'d and is renamed: compared up to renaming *)
val _ = \<^assert> (same_shape (Thm.prop_of @{thm h2}, Logic.varify_global \<^prop>\<open>LF (q :: ('c, 'd) ring_scheme) \<Longrightarrow> Pc c y\<close>));
val _ = \<^assert> (Thm.nprems_of @{thm h2} = 1 andalso Exported_Premises.count_of @{thm h2} = 1);
\<close>
local_setup \<open>fn lthy =>
  let
    val (ths, lthy') = lemmas_in lthy "hz" "LF.fooP" "[of _ \"c :: 'z\"]";
    val has_z = exists (fn ((a, _), _) => a = "'z") (Term.add_tvars (Thm.prop_of (the_single ths)) []);
  in \<^assert> has_z; lthy' end\<close>
ML_val \<open>
fun has_z th = exists (fn ((a, _), _) => a = "'z") (Term.add_tvars (Thm.prop_of th) []);
val _ = \<^assert> (has_z @{thm hz} andalso has_z @{thm LF.hz});
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm hz}, the_single (the (Symtab.lookup heavy2 "hz"))));
\<close>
lemmas h4 = LF.fooP[of _ "\<one>\<^bsub>UP S\<^esub>"]
lemmas hS0 = LF.fooS[of _ "\<one>\<^bsub>UP S\<^esub>"]
lemmas hS1 = LF.fooS[OF LF_axioms, of "\<one>\<^bsub>UP S\<^esub>"]
context fixes d :: 'a begin
lemmas h3' = LF.fooP[of _ d]
end
context fixes q :: "nat \<Rightarrow> 'a" begin
lemmas hS = LF.fooS[of _ q]
end
lemma th: "Qc c" apply (insert LF_axioms) by (rule Qc1_ax)
lemmas hq = LF.fooQ[OF _ th]
lemmas hq' = LF.fooQ[OF LF_axioms th]
lemmas cj = conjI
lemmas hm = monoid.r_one
ML_val \<open>
val lp = Light_Locale_Axiom_Facts.is_light_prop \<^context>;
val _ = \<^assert> (lp \<^prop>\<open>LF S\<close> andalso lp \<^prop>\<open>LF2 S R\<close>);
val _ = \<^assert> (not (lp \<^prop>\<open>monoid G\<close>) andalso not (lp \<^prop>\<open>D S\<close>));
\<close>
context fixes y :: nat assumes "y \<le> y" begin
lemmas hle = order_trans
end
context fixes y z :: "'c::linorder" assumes "y < z" begin
lemmas h7 = less_imp_neq
end
context fixes g2 defines "g2 \<equiv> h S" begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.bad" "[elim]")
  in
    (* LF.bad is already an elim rule of the theory (lemma bad [elim] above), so stock reports
       "Ignoring duplicate unsafe elimination (elim)" (section 11, item (19)); nothing else *)
    \<^assert> (forall (String.isPrefix "Ignoring duplicate") w); lthy'
  end\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.bad} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Sc x\<close>);
val _ = \<^assert> (exists (fn (key, plain, _) =>
    Exported_Premises.count_of key = 1 andalso Thm.nprems_of key = 2 andalso
    major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth (Thm.prems_of plain) 1))
  (claset_entries \<^context> @{thm LF.bad}));
\<close>
lemmas hg = LF.fooP[of _ g2]
end
lemmas hc = LF.fooP[of _ cabb]

(* tags and redeclaration *)
lemmas h5 [case_names a b] = LF.foo
lemmas h5' = LF.foo
ML_val \<open>
val _ = \<^assert> (not (AList.defined (op =) (Thm.get_tags @{thm h5'}) "consumes"));
val _ = \<^assert> (not (AList.defined (op =) (Thm.get_tags @{thm h5'}) "case_names"));
val _ = \<^assert> (Exported_Premises.count_of @{thm h5'} = 1 andalso Rule_Cases.get_consumes @{thm h5'} = 1);
\<close>
declare LF.foo[cases pred: Rc]
ML_val \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm LF.foo};
val _ = \<^assert> (diff_K (e, heavy2_foo_entry) andalso Exported_Premises.count_of e = 1);
\<close>
lemmas h6 [rotated, consumes 1] = LF.foo
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.h6} aconv Logic.varify_global \<^prop>\<open>A \<Longrightarrow> B \<Longrightarrow> LF S \<Longrightarrow> A \<and> B\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.h6} = 0);
(* negative: LF_axioms is silently put into ?A *)
val _ = \<^assert> (exists_subterm (fn t => t aconv \<^term>\<open>LF S\<close>) (Thm.concl_of @{thm LF.h6 [OF LF_axioms]}));
\<close>
lemmas foo7 [consumes 1] = LF.foo[OF LF_axioms]
lemmas foo7' = LF.foo[OF _ LF_axioms]
ML_val \<open>
val _ = \<^assert> (Thm.nprems_of @{thm foo7'} = 2 andalso
  Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm foo7'})) andalso
  exists_subterm (fn t => t aconv \<^term>\<open>LF S\<close>) (Thm.concl_of @{thm foo7'}));
val _ = \<^assert> (Thm.concl_of @{thm LF.tr.induct [OF _ LF_axioms]} aconv \<^prop>\<open>LF S\<close>);
\<close>
lemmas fr2 [dest] = LF.fr0[rule_format]
lemmas fr' [dest] = LF.fr0b[OF LF_axioms, rule_format]
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm fr2} = 0);
val tctxt = thy_ctxt \<^context>;
(* the registrations of the theory copies LF.fr2 and LF.fr', read from the theory claset *)
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fr2} = 0);
val _ = \<^assert> (exists (fn (_, plain, _) => Light_Locale_Axiom_Facts.is_light_prop tctxt (Thm.major_prem_of plain))
  (claset_entries tctxt @{thm LF.fr2}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fr'} = 1);
val _ = \<^assert> (exists (fn (_, plain, _) => same_shape (Thm.prop_of plain,
    Logic.varify_global \<^prop>\<open>Qc x S \<Longrightarrow> LF S \<Longrightarrow> (Rc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>))
  (claset_entries tctxt @{thm LF.fr'}));
\<close>
lemmas r' [cases type: T] = LF.Abs_T_cases
ML_val \<open>
val SOME e = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm LF.r'};
val _ = \<^assert> (diff_K (e, heavy2_r'_entry) andalso Exported_Premises.count_of e = 1);
val _ = \<^assert> (is_some (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>tr0\<close> @{thm LF.trS}));
\<close>
declare LF.foo9[cases pred: Rc]
declare LF.ip.cases [cases pred: ip]
lemmas ipc [case_names Z S, consumes 1] = LF.ip.cases
ML_val \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm LF.foo9};
val _ = \<^assert> (diff_K (e, heavy2_foo9_entry) andalso Exported_Premises.count_of e = 1);
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm LF.ip.cases};
val _ = \<^assert> (diff_K (e, heavy2_ipcases_entry) andalso Exported_Premises.count_of e = 1);
val _ = \<^assert> (diff_K (@{thm ipc}, the_single (the (Symtab.lookup heavy2 "ipc"))));
\<close>
(* the simp row of milestone 1: the theory copy's condition closed by hand *)
ML_val \<open>\<^assert> (proves (fn c => simp_tac (c addsimps [@{thm LF.aux [OF LF_axioms]}]) 1) \<^context> \<^prop>\<open>gc (hc 0) = 0\<close>)\<close>
end

context LF2 begin
lemmas hR1 = LF2.fooR[of _ _ "g S"]
lemmas hR2 = LF2.fooR[of _ R "g S"]
lemmas hp = LF.fooP
end

lemma (in LF) ax: "Pc S y" by (rule Pc_ax)
lemma (in LF) fa7 [OF LF.ax[OF LF_axioms]]: "Pc S y \<Longrightarrow> Pc S y \<and> Pc S y" by (rule conjI)

ML \<open>
val H2 = the_single o the o Symtab.lookup heavy2;
val LFp = \<^const_name>\<open>LF\<close> and Dp = \<^const_name>\<open>D\<close>;
fun one_light th = length (filter (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of th)) = 1;

(* the redeclarations of LF.*: nprems LF.x = nprems D.x - 1 (the theory copy D.x is the oracle);
   phi-equal to the twin's block copy of the same row (one predicate premise there) *)
fun D_copy n = Proof_Context.get_thm \<^context> ("D." ^ n);
fun LF_copy n = Proof_Context.get_thm \<^context> ("LF." ^ n);
val _ = map (fn n => \<^assert> (Thm.nprems_of (LF_copy n) = Thm.nprems_of (D_copy n) - 1))
  ["h", "h2", "hz", "h4", "hS0", "hS"];
(* hS1's block form carries the hyp LF S and goes the stock way: the same count as the twin *)
val _ = \<^assert> (Thm.nprems_of (LF_copy "hS1") = Thm.nprems_of (D_copy "hS1"));
(* the rows not mentioning the block's S: phi-equal to the twin's block copy of the same row *)
val _ = map (fn n => \<^assert> (phi_equal (LFp, Dp) (LF_copy n, H2 n))) ["h", "h2", "hz"];
val _ = \<^assert> (Thm.prop_of @{thm LF.h} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc c y\<close>);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h} = 1 andalso Exported_Premises.count_of @{thm LF.h} = 1);
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.h2},
  Logic.varify_global \<^prop>\<open>LF (q :: ('c, 'd) ring_scheme) \<Longrightarrow> Pc c y\<close>));
val _ = \<^assert> (Thm.nprems_of @{thm LF.h2} = 1 andalso Exported_Premises.count_of @{thm LF.h2} = 1);
val _ = \<^assert> (phi_equal (LFp, Dp) (@{thm LF.h2}, H2 "h2"));
val _ = \<^assert> (phi_equal (LFp, Dp) (@{thm LF.hz}, H2 "hz"));
(* ?S and ?Sa are two variables of the same type; type variables renamed on export: same_shape *)
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.h4},
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc \<one>\<^bsub>UP (Sa :: ('a, 'b) ring_scheme)\<^esub> y\<close>));
val _ = \<^assert> (length (Term.add_vars (Thm.prop_of @{thm LF.h4}) []) = 3);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h4} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF.hS0} = 1 andalso Thm.nprems_of @{thm LF.hS1} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF.hS} = 1 andalso Thm.nprems_of (D_copy "hS") = 2);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h3'} = 1 andalso Exported_Premises.count_of @{thm LF.h3'} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF2.hR1} = 1 andalso Thm.nprems_of @{thm LF2.hR2} = 1);
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF2.hp}, @{thm LF.fooP}) andalso Exported_Premises.count_of @{thm LF2.hp} = 1
  andalso Thm.nprems_of @{thm LF2.hp} = Thm.nprems_of @{thm D2.hp} - 1);
(* the derived facts *)
val _ = \<^assert> (Thm.nprems_of @{thm LF.hq} = 2 andalso Exported_Premises.count_of @{thm LF.hq} = 1 andalso
  forall (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of @{thm LF.hq}) andalso
  same_shape (Thm.concl_of @{thm LF.hq}, Logic.varify_global \<^prop>\<open>Pc c y\<close>));
val _ = \<^assert> (Thm.prop_of @{thm LF.hq'} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc c y\<close>
  andalso Exported_Premises.count_of @{thm LF.hq'} = 1);
(* non-LF facts get the premise as in stock *)
val _ = \<^assert> (Thm.prop_of @{thm LF.cj} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q\<close>);
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.hm} = 1 andalso Thm.nprems_of @{thm LF.hm} = Thm.nprems_of (D_copy "hm")
  andalso Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.hm}))
  andalso not (Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth (Thm.prems_of @{thm LF.hm}) 1)));
(* nested assumes: the ?a <= ?b premise stays; the sort row *)
val _ = \<^assert> (Thm.nprems_of @{thm LF.hle} = 4 andalso Exported_Premises.count_of @{thm LF.hle} = 2);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h7} = 3 andalso Exported_Premises.count_of @{thm LF.h7} = 2);
val _ =
  (case map (Term.strip_comb o HOLogic.dest_Trueprop) (Thm.prems_of @{thm LF.h7}) of
    [_, (_, [Var (_, T1), _]), (_, [Var (_, T2), _])] =>
      \<^assert> (T1 = TVar (("'c", 0), \<^sort>\<open>linorder\<close>) andalso
        (case T2 of TVar (_, S) => S = \<^sort>\<open>order\<close> | _ => false))
  | _ => raise Fail "h7 shape");
(* nested defines: hg and hc have no g2 / cabb, the shape LF ?S ==> Pc (h ?Sa) ?y *)
val hg_shape = Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc (h (Sa :: ('a, 'b) ring_scheme)) y\<close>;
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.hg}, hg_shape) andalso Exported_Premises.count_of @{thm LF.hg} = 1);
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.hc}, hg_shape) andalso Exported_Premises.count_of @{thm LF.hc} = 1);
val _ = \<^assert> (length (Term.add_vars (Thm.prop_of @{thm LF.hg}) []) = 3);
val _ = \<^assert> (not (exists_Const (fn (c, _) => Long_Name.base_name c = "cabb") (Thm.prop_of @{thm LF.hc})));
(* tags *)
val _ = \<^assert> (Thm.prop_of @{thm LF.h5} aconv Thm.prop_of @{thm LF.foo});
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.h5} = 1 andalso
  not (AList.defined (op =) (Thm.get_tags @{thm LF.h5}) "consumes") andalso Rule_Cases.get_consumes @{thm LF.h5} = 1);
val _ = \<^assert> (diff_K (@{thm LF.h5}, H2 "h5"));
val _ = \<^assert> (diff_K (@{thm LF.foo7}, H2 "foo7") andalso Rule_Cases.get @{thm LF.foo7} = ([(("1", []), [])], 2));
val _ = \<^assert> (Thm.nprems_of @{thm LF.foo7'} = 3);
val _ = \<^assert> (diff_K (@{thm LF.r'}, H2 "r'"));
val _ = \<^assert> (is_some (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.r'}));
val _ = \<^assert> (diff_K (@{thm LF.ipc}, H2 "ipc"));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fa7} = 1 andalso one_light @{thm LF.fa7});
(* theory level: lemma (in LF) fa6 [OF ax] reports Undefined fact *)
val _ = \<^assert>
  ((lemma_in "LF" (Binding.name "fa6") "[OF ax]" "Pc S y \<Longrightarrow> Pc S y" (fn ctxt => assume_tac ctxt) \<^theory>; false)
    handle ERROR msg => String.isPrefix "Undefined fact" (plain msg));
(* the theory-level goal without predicate facts does not close by simp *)
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>gc (hc 0) = 0\<close>));
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>LF.Leaf \<noteq> LF.Node a b\<close>));
\<close>

end
