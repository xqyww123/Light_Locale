(* Plan section 7 test 6, the declaration-block leaf (plan lines 4211-4295, 4311-4372, 4389-4396, section 11
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
   rows of plan lines 4239-4295 and 4311-4338 against the premise-count oracle D.x and the twin's
   rows, the tag rows h5/h5'/h6/foo7/foo7', fr2/fr', r', trS, foo9/ip.cases/ipc, fa6/fa7, the simp
   row of milestone 1 and the theory-level negatives. *)
theory Test6_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun facts_of ctxt names = Symtab.make (map (fn n => (n, Proof_Context.get_fact ctxt (Facts.named n))) names);
(* the rows of the declaration block and how each is compared: the local copy with the heavy block
   fact (plain equality, or the three items where the statement names the predicate or a block
   constant), the theory copy with the heavy block fact (block_lemma, K 1) or, for the package
   rows, with D.x under phi and with the heavy block fact up to K 1 *)
datatype row = Plain | Three | Package;
val rows =
  [("fd_def", Package), ("f.simps", Package), ("ev.intros", Package), ("ip.intros", Package),
   ("ip.cases", Package), ("ip.inducts", Package), ("ipz.cases", Package), ("ipz.inducts", Package),
   ("tr.induct", Package), ("Abs_T_cases", Package), ("bar_def", Package),
   ("bad", Plain), ("fooP", Plain), ("fooQ", Plain), ("fooS", Plain), ("fooT", Plain), ("fooV", Plain),
   ("triv", Plain), ("triv2", Plain), ("foo", Plain), ("foo4", Plain), ("fr", Plain), ("fr0", Plain),
   ("fr0b", Plain), ("foo9", Plain), ("r0z", Three), ("trS", Plain), ("aux", Plain), ("a", Plain),
   ("b", Plain), ("fa3", Plain), ("fa3b", Three), ("fa3c", Plain), ("fa4", Plain)];
val block_names = map #1 rows;
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

(* table check right after inductive ip: the theory copies in the theory's table, up to K 1
   against the heavy block facts -- defined once, run here and again when the block is reopened
   (plan line 4668) -- and the local copy in the block's table *)
ML \<open>
val H = the o Symtab.lookup heavy;
fun ip_table_check ctxt =
  let
    val tctxt = thy_ctxt ctxt;
    val key = \<^prop>\<open>ip x\<close>;
    val _ = \<^assert> (diff_K 1 (the (induct_entry Induct.find_casesP tctxt key @{thm LF.ip.cases}), the_single (H "ip.cases")));
    val _ = map2 (fn th => fn hth => \<^assert> (diff_K 1 (the (induct_entry Induct.find_inductP tctxt key th), hth)))
      @{thms LF.ip.inducts} (H "ip.inducts");
  in () end;
\<close>
ML_val \<open>
val _ = ip_table_check \<^context>;
val SOME e' = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm ip.cases};
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
val L = the o Symtab.lookup light;
val _ = List.app (fn (n, kind) =>
  \<^assert> (eq_list (case kind of Plain => plain_equal | _ => three_items) (L n, H n))) rows;

(* the table checks of lemma foo9 [cases pred: Rc] and r0z [consumes 0, cases pred: ip]: the theory
   copies in the theory's table, up to K 1 against the heavy block facts (section 11, item (19)) *)
val tctxt = thy_ctxt \<^context>;
val _ = \<^assert> (diff_K 1 (the (induct_entry Induct.find_casesP tctxt \<^prop>\<open>Rc x S\<close> @{thm LF.foo9}), the_single (H "foo9")));
val _ = \<^assert> (diff_K 1 (the (induct_entry Induct.find_casesP tctxt \<^prop>\<open>ip x\<close> @{thm LF.r0z}), the_single (H "r0z")));

(* the same-name pair: the block's bar_def unfolds, LF.bar_def is conditional and does not *)
val no_bar = not o exists_Const (fn (c, _) => Long_Name.base_name c = "bar") o Thm.prop_of;
val _ = \<^assert> (no_bar @{thm fa3} andalso not (no_bar @{thm fa3b}) andalso no_bar @{thm fa3c});

(* the threaded row: (1) above; (5) the block simpset lists a's rule and not b's *)
val simps = simp_props \<^context>;
val _ = \<^assert> (exists (fn p => #1 (Logic.dest_equals (Logic.strip_imp_concl p)) aconv \<^term>\<open>fz S\<close>) simps);
val _ = \<^assert> (not (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>gz\<close>)) simps));

(* fr: the derived dest rule's major premise is Pc ?x in the block *)
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Pc\<close> plain) (claset_entries \<^context> @{thm fr}));
\<close>

end

(* the theory copies against the heavy block facts (lemma rows) and D.x under phi (package rows);
   the ML command binds only what cannot fail, the rows are ML_val commands *)
ML \<open>
val LFp = \<^const_name>\<open>LF\<close> and Dp = \<^const_name>\<open>D\<close>;
fun LF_facts ctxt n = Proof_Context.get_fact ctxt (Facts.named ("LF." ^ n));
fun D_facts ctxt n = Proof_Context.get_fact ctxt (Facts.named ("D." ^ n));
val simps = simp_props \<^context>;
\<close>
ML_val \<open>
check_rows (map (fn (n, kind) => (n, fn () =>
    (case kind of
      Package =>
        eq_list (phi_equal (LFp, Dp)) (LF_facts \<^context> n, D_facts \<^context> n) andalso
        eq_list (diff_K 1) (LF_facts \<^context> n, H n)
    | _ => eq_list (block_lemma ("LF", "D") 1) (LF_facts \<^context> n, H n)))) rows)
\<close>

(* pinned shapes *)
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.fooP} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc x y\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooQ} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc x \<Longrightarrow> Pc x y\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooT} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc S\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LF.fooV} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> A \<or> B\<close>);
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.triv} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B\<close>
  andalso Exported_Premises.count_of @{thm LF.triv} = 1 andalso Thm.nprems_of @{thm LF.triv} = 3);
val _ = \<^assert> (Thm.prop_of @{thm LF.triv2} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B\<close>
  andalso Exported_Premises.count_of @{thm LF.triv2} = 1
  andalso Rule_Cases.get @{thm LF.triv2} = ([(("a", []), []), (("b", []), [])], 1));
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.foo} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
  andalso Exported_Premises.count_of @{thm LF.foo} = 1
  andalso Rule_Cases.get @{thm LF.foo} = ([(("a", []), []), (("b", []), [])], 2));
val _ = \<^assert> (Thm.prop_of @{thm LF.foo4} aconv
    Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Sc (y :: 'd) \<Longrightarrow> Pc (x :: 'c) \<Longrightarrow> Qc x y\<close>
  andalso Exported_Premises.count_of @{thm LF.foo4} = 1 andalso #2 (Rule_Cases.get @{thm LF.foo4}) = 2);
\<close>
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fr} = 1);
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Pc\<close> plain) (claset_entries \<^context> @{thm LF.fr}));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.b} = 1 andalso Thm.nprems_of @{thm LF.b} = 1
  andalso Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.b}))
  andalso Thm.concl_of @{thm LF.b} aconv \<^prop>\<open>gz kz = kc\<close>);
\<close>
ML_val \<open>
(* the simplifier renumbers the rule's variables (LF ?S1 ==> fz ?S1 == kz): structural check *)
val _ = \<^assert> (exists (fn p =>
    (case Logic.dest_equals (Logic.strip_imp_concl p) of
      (Const (c, _) $ Var _, Const (k, _)) => c = \<^const_name>\<open>fz\<close> andalso k = \<^const_name>\<open>kz\<close>
    | _ => false) andalso
    length (Logic.strip_imp_prems p) = 1 andalso
    Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Logic.strip_imp_prems p))) simps);
val _ = \<^assert> (not (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>gz\<close>)) simps));
\<close>
ML_val \<open>
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
   check with the same text on both sides, a declare row with the same loose variables goes
   through (section 11, item (19)) *)
ML \<open>
fun loose_a_rejected msg =
  let val m = Protocol_Message.clean_output msg
  in String.isPrefix "Malformed global fact" m andalso String.isSubstring "Illegal fixed variable: \"a\"" m end;
\<close>
context DM begin
lemma fa5 [where x = "a \<otimes> b" for a b]: "x = x" by (rule refl)
lemma hbase: "Pc x" by (rule Pc1_ax)
ML \<open>val heavy_m = @{thm fa5};\<close>
ML_val \<open>\<^assert> ((lemmas_in \<^context> "fa5y" "hbase" "[where x = \"a \<otimes> b\"]"; false)
  handle ERROR msg => loose_a_rejected msg)\<close>
declare hbase[where x = "a \<otimes> b", simp]
end

context LM begin
lemma fa5 [where x = "a \<otimes> b" for a b]: "x = x" by (rule refl)
ML_val \<open>\<^assert> (plain_equal (@{thm fa5}, heavy_m))\<close>
ML_val \<open>\<^assert> ((theorem_in \<^context> (Binding.name "fa5b") "[where x = \"a \<otimes> b\"]" "x = x"
    (fn ctxt => resolve_tac ctxt @{thms refl}); false)
  handle ERROR msg => loose_a_rejected msg)\<close>
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
  (simp_props \<^context>));
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
context fixes d :: 'a begin
lemmas h3' = D.fooP[of _ d]
end
context fixes q :: "nat \<Rightarrow> 'a" begin
lemmas hS = D.fooS[of _ q]
end
lemma th: "Qc c" apply (insert D_axioms) by (rule Qc1_ax)
lemmas hq = D.fooQ[OF _ th]
lemmas hq' = D.fooQ[OF D_axioms th]
lemmas cj = conjI
lemmas hm = monoid.r_one
context fixes y :: nat assumes "y \<le> y" begin
lemmas hle = order_trans
end
context fixes y z :: "'c::linorder" assumes "y < z" begin
lemmas h7 = less_imp_neq
end
context fixes g2 defines "g2 \<equiv> h S" begin
lemmas hg = D.fooP[of _ g2]
end
lemmas hc = D.fooP[of _ cabb]
lemmas h5 [case_names a b] = foo
declare foo [cases pred: Rc]
lemmas foo7 [consumes 1] = foo
lemmas r' [cases type: T] = Abs_T_cases
declare foo9 [cases pred: Rc]
declare ip.cases [cases pred: ip]
lemmas ipc [case_names Z S, consumes 1] = ip.cases
ML \<open>
val heavy2 = facts_of \<^context> ["h", "h2", "hz", "h5", "foo7", "r'", "ipc"];
val heavy2_foo_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm foo});
val heavy2_foo9_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm foo9});
val heavy2_ipcases_entry = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm ip.cases});
val heavy2_r'_entry = the (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm r'});
\<close>
end

context D2 begin
lemmas hp = D.fooP
lemmas hR1 = D2.fooR[of _ _ "g S"]
lemmas hR2 = D2.fooR[of _ R "g S"]
end

context LF begin

(* plan lines 4239-4241: in the reopened block the goal closes by the theory-level registration
   of LF.bad (major premise Rc ?x ?S, LF ?S second, closed by LF_axioms) -- read before anything
   is redeclared *)
ML_val \<open>\<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>)\<close>

(* declare LF.bad[rotated, elim]: LF.bad is stored unchanged, the rotated instance is registered
   with K 0, its major premise Rc ?x ?S and LF ?S second *)
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
\<close>

lemmas h = LF.fooP[of _ c]
context fixes q :: "('c, 'd) ring_scheme" begin
lemmas h2 = LF.fooP[of q c]
end
ML_val \<open>
(* h2 in the outer block after the nested end: no Free q, instantiable *)
val _ = \<^assert> (not (exists (fn (x, _) => x = "q") (Term.add_frees (Thm.prop_of @{thm h2}) [])));
val _ = @{thm h2 [of S]};  (*instantiable: a compile-time failure fails the leaf*)
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
(* the declare row of the nested defines block takes a fresh fixture: LF.bad is already an elim
   rule of the theory (lemma bad [elim] of the declaration block), so declaring it again would be
   dropped as a duplicate (section 11, item (19)) *)
lemma bad0: "Rc x S \<Longrightarrow> Qc x" by (rule Qc1_ax)
context fixes g2 defines "g2 \<equiv> h S" begin
ML_val \<open>\<^assert> (forall (fn ctxt => null (claset_entries ctxt @{thm LF.bad0})) [\<^context>, thy_ctxt \<^context>])\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.bad0" "[elim]")
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.bad0} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Rc x S \<Longrightarrow> Qc x\<close>);
(* the registration, in the nested block and at theory level: the K 1 key, the derived rule's
   major premise Rc ?x ?S, LF ?S second *)
fun registered ctxt =
  let val (key, plain) = claset_rule ctxt Bires.elim_kind @{thm LF.bad0} in
    Exported_Premises.count_of key = 1 andalso Thm.nprems_of key = 2 andalso
    major_is \<^const_name>\<open>Rc\<close> plain andalso
    Light_Locale_Axiom_Facts.is_light_prop ctxt (nth (Thm.prems_of plain) 1)
  end;
val _ = \<^assert> (forall registered [\<^context>, thy_ctxt \<^context>]);
\<close>
lemmas hg = LF.fooP[of _ g2]
end
(* the outer block's hg after the nested end: g2 unfolded, h S in its place *)
ML_val \<open>
val _ = \<^assert> (not (exists (fn (x, _) => x = "g2") (Term.add_frees (Thm.prop_of @{thm hg}) [])));
val _ = \<^assert> (exists_Const (fn (c, _) => c = \<^const_name>\<open>h\<close>) (Thm.prop_of @{thm hg}));
\<close>
lemmas hc = LF.fooP[of _ cabb]

(* tags and redeclaration *)
lemmas h5 [case_names a b] = LF.foo
lemmas h5' = LF.foo
(* h5' is LF.foo itself (second version: a redeclaration whose export changes nothing keeps the
   theorem and its tags) *)
ML_val \<open>\<^assert> (AList.lookup (op =) (Thm.get_tags @{thm h5'}) "consumes" = SOME "2")\<close>
ML_val \<open>\<^assert> (AList.defined (op =) (Thm.get_tags @{thm h5'}) "case_names")\<close>
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm h5'} = 1 andalso Rule_Cases.get_consumes @{thm h5'} = 2)\<close>
declare LF.foo[cases pred: Rc]
(* the table entry is LF.foo itself: its case names a b and consumes 2 *)
ML_val \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm LF.foo};
val _ = \<^assert> (Rule_Cases.get e = Rule_Cases.get @{thm LF.foo} andalso Exported_Premises.count_of e = 1);
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
(* fr2: rule_format keeps K (second version), so fr2 and the theory copy LF.fr2 are
   LF ?S ==> Qc ?x ==> Pc ?x with K 1 and the theory-level dest rule's major premise is Qc ?x *)
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fr2} = 1)\<close>
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm LF.fr2} = 1)\<close>
ML_val \<open>
val tctxt = thy_ctxt \<^context>;
val _ = \<^assert> (exists (fn (_, plain, _) => same_shape (Thm.major_prem_of plain, Logic.varify_global \<^prop>\<open>Qc (x :: 'c)\<close>))
  (claset_entries tctxt @{thm LF.fr2}));
\<close>
(* fr': OF clears K first, the stock export gives K 1 *)
ML_val \<open>
val tctxt = thy_ctxt \<^context>;
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fr'} = 1);
val _ = \<^assert> (exists (fn (_, plain, _) => same_shape (Thm.prop_of plain,
    Logic.varify_global \<^prop>\<open>Qc x S \<Longrightarrow> LF S \<Longrightarrow> (Rc x \<Longrightarrow> PROP W) \<Longrightarrow> PROP W\<close>))
  (claset_entries tctxt @{thm LF.fr'}));
\<close>
lemmas r' [cases type: T] = LF.Abs_T_cases
(* r' is LF.Abs_T_cases itself, its case name Abs_T kept *)
ML_val \<open>
val SOME e = induct_entry Induct.find_casesT \<^context> \<^typ>\<open>T\<close> @{thm LF.r'};
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.r'}, @{thm LF.Abs_T_cases}) andalso
  Rule_Cases.get e = Rule_Cases.get @{thm LF.Abs_T_cases} andalso Exported_Premises.count_of e = 1);
\<close>
ML_val \<open>\<^assert> (is_some (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>tr0\<close> @{thm LF.trS}))\<close>
(* the registrations of the declaration block are still there when the block is reopened *)
ML_val \<open>ip_table_check \<^context>\<close>
declare LF.foo9[cases pred: Rc]
declare LF.ip.cases [cases pred: ip]
lemmas ipc [case_names Z S, consumes 1] = LF.ip.cases
ML_val \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm LF.foo9};
val _ = \<^assert> (diff_K 1 (e, heavy2_foo9_entry));
\<close>
(* the entry is LF.ip.cases itself, its case names z / s kept *)
ML_val \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>ip x\<close> @{thm LF.ip.cases};
val _ = \<^assert> (Rule_Cases.get e = Rule_Cases.get @{thm LF.ip.cases} andalso Exported_Premises.count_of e = 1);
\<close>
ML_val \<open>\<^assert> (diff_K (Light_Locale_Axiom_Facts.premise_count \<^context>) (@{thm ipc}, the_single (the (Symtab.lookup heavy2 "ipc"))))\<close>
(* the simp row of milestone 1: the theory copy's condition closed by hand *)
ML_val \<open>\<^assert> (proves (fn c => simp_tac (c addsimps [@{thm LF.aux [OF LF_axioms]}]) 1) \<^context> \<^prop>\<open>gc (hc 0) = 0\<close>)\<close>

(* N17, the final criterion and the way a redeclaration is stored (second version).  A
   redeclaration without hyps whose export changes nothing is stored as the theorem itself, tags
   included: my_induct (nat.induct, K 0), y (LF.foo, K 1), yt (a tag t of its own); one whose
   export changes it goes through light_export, which only generalises and keeps K and the
   Rule_Cases tags: yi = LF.foo[of S]; z and z2 mention the block's S; a fact written back by
   ML Local_Theory.note is not a redeclaration and goes the stock way *)
lemmas my_induct = nat.induct
lemmas y = LF.foo
lemmas yi = LF.foo[of S]
lemmas yt = LF.foo [tagged t v]
lemmas z = LF.foo[of S, THEN conjunct1]
lemmas z2 = conjI[of "P S" for P]
local_setup \<open>Local_Theory.note ((\<^binding>\<open>nc\<close>, []), @{thms conjI}) #> snd\<close>
local_setup \<open>Local_Theory.note ((\<^binding>\<open>nf\<close>, []), @{thms LF.foo}) #> snd\<close>
ML_val \<open>\<^assert> (Rule_Cases.get @{thm yi} = Rule_Cases.get @{thm LF.yi})\<close>
ML_val \<open>\<^assert> (AList.lookup (op =) (Thm.get_tags @{thm yt}) "t" = SOME "v")\<close>
end

ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.my_induct}, @{thm nat.induct}) andalso not (has_K_tag @{thm LF.my_induct})
  andalso Rule_Cases.get @{thm LF.my_induct} = Rule_Cases.get @{thm nat.induct});
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.y}, @{thm LF.foo}) andalso Exported_Premises.count_of @{thm LF.y} = 1
  andalso Rule_Cases.get @{thm LF.y} = Rule_Cases.get @{thm LF.foo});
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.yi} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
  andalso Exported_Premises.count_of @{thm LF.yi} = 1
  andalso Rule_Cases.get @{thm LF.yi} = ([(("a", []), []), (("b", []), [])], 2));
\<close>
ML_val \<open>\<^assert> (AList.lookup (op =) (Thm.get_tags @{thm LF.yt}) "t" = SOME "v")\<close>
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.z}, Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A\<close>)
  andalso not (has_K_tag @{thm LF.z}));
\<close>
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.z2},
    Logic.varify_global \<^prop>\<open>P (S :: ('a, 'b) ring_scheme) \<Longrightarrow> Q \<Longrightarrow> P S \<and> Q\<close>)
  andalso not (has_K_tag @{thm LF.z2}));
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.nc} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q\<close>
  andalso Exported_Premises.count_of @{thm LF.nc} = 1);
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.nprems_of @{thm LF.nf} = 4 andalso Exported_Premises.count_of @{thm LF.nf} = 2 andalso
  forall (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (take 2 (Thm.prems_of @{thm LF.nf})));
\<close>

context LF2 begin
lemmas hR1 = LF2.fooR[of _ _ "g S"]
lemmas hR2 = LF2.fooR[of _ R "g S"]
lemmas hp = LF.fooP
end

lemma (in LF) ax: "Pc S y" by (rule Pc_ax)
lemma (in LF) fa7 [OF LF.ax[OF LF_axioms]]: "Pc S y \<Longrightarrow> Pc S y \<and> Pc S y" by (rule conjI)

(* the bindings of the rows (an ML command stops the theory on failure, so it binds only what
   cannot fail); the rows are ML_val commands *)
ML \<open>
val H2 = the_single o the o Symtab.lookup heavy2;
val LF_copy = the_single o LF_facts \<^context> and D_copy = the_single o D_facts \<^context>;
fun one_light th = length (light_prems \<^context> th) = 1;
val hg_shape = Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc (h (Sa :: ('a, 'b) ring_scheme)) y\<close>;
\<close>

(* the premise-count oracle of the redeclaration rows (plan lines 4232-4233), one row (name, delta, K):
   the theory copy D.x of the twin's row; nprems LF.x = nprems D.x + delta, delta -1 where the row
   is stored unchanged (its exported form has the one light premise D.x gets on top of its own),
   0 where the block form carries the hyp LF S and goes the stock way (hS1, hq, hq'), K 1 (section
   11, item (19)); the facts that are not LF facts (cj, hm, hle, h7) are redeclarations stored as
   the theorems themselves since the second version, checked in their own rows below *)
ML_val \<open>
check_rows (map (fn (n, delta, k) =>
    (n, fn () => Thm.nprems_of (LF_copy n) = Thm.nprems_of (D_copy n) + delta andalso
      Exported_Premises.count_of (LF_copy n) = k))
  [("h", ~1, 1), ("h2", ~1, 1), ("hz", ~1, 1), ("h4", ~1, 1), ("hS0", ~1, 1), ("hS", ~1, 1), ("h3'", ~1, 1),
   ("hg", ~1, 1), ("hc", ~1, 1), ("hS1", 0, 1), ("hq", 0, 1), ("hq'", 0, 1)]);
\<close>
ML_val \<open>
check_rows (map (fn (l, d) =>
    (l, fn () => Thm.nprems_of (Proof_Context.get_thm \<^context> l) = Thm.nprems_of (Proof_Context.get_thm \<^context> d) - 1
      andalso Exported_Premises.count_of (Proof_Context.get_thm \<^context> l) = 1))
  [("LF2.hR1", "D2.hR1"), ("LF2.hR2", "D2.hR2")]);
\<close>
(* the rows not mentioning the block's S: phi-equal to the twin's block copy of the same row *)
ML_val \<open>check_rows (map (fn n => (n, fn () => phi_equal (LFp, Dp) (LF_copy n, H2 n))) ["h", "h2", "hz"])\<close>
(* the shapes *)
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.h} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc c y\<close>);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h} = 1);
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.h2},
  Logic.varify_global \<^prop>\<open>LF (q :: ('c, 'd) ring_scheme) \<Longrightarrow> Pc c y\<close>));
val _ = \<^assert> (Thm.nprems_of @{thm LF.h2} = 1);
(* ?S and ?Sa are two variables of the same type; type variables renamed on export: same_shape *)
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.h4},
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc \<one>\<^bsub>UP (Sa :: ('a, 'b) ring_scheme)\<^esub> y\<close>));
val _ = \<^assert> (length (Term.add_vars (Thm.prop_of @{thm LF.h4}) []) = 3);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h4} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF.hS0} = 1 andalso Thm.nprems_of @{thm LF.hS1} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF.hS} = 1 andalso Thm.nprems_of (D_copy "hS") = 2);
val _ = \<^assert> (Thm.nprems_of @{thm LF.h3'} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LF2.hR1} = 1 andalso Thm.nprems_of @{thm LF2.hR2} = 1);
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF2.hp}, @{thm LF.fooP}) andalso Exported_Premises.count_of @{thm LF2.hp} = 1
  andalso Thm.nprems_of @{thm LF2.hp} = Thm.nprems_of @{thm D2.hp} - 1);
\<close>
(* the derived facts *)
ML_val \<open>
val _ = \<^assert> (Thm.nprems_of @{thm LF.hq} = 2 andalso
  forall (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of @{thm LF.hq}) andalso
  same_shape (Thm.concl_of @{thm LF.hq}, Logic.varify_global \<^prop>\<open>Pc c y\<close>));
val _ = \<^assert> (Thm.prop_of @{thm LF.hq'} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Pc c y\<close>);
\<close>
(* nested defines: hg and hc have no g2 / cabb, the shape LF ?S ==> Pc (h ?Sa) ?y *)
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.hg}, hg_shape));
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.hc}, hg_shape));
val _ = \<^assert> (length (Term.add_vars (Thm.prop_of @{thm LF.hg}) []) = 3);
val _ = \<^assert> (not (exists_Const (fn (c, _) => Long_Name.base_name c = "cabb") (Thm.prop_of @{thm LF.hc})));
\<close>
(* tags *)
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.h5} aconv Thm.prop_of @{thm LF.foo});
val _ = \<^assert> (diff_K 1 (@{thm LF.foo7}, H2 "foo7") andalso Rule_Cases.get @{thm LF.foo7} = ([(("1", []), [])], 2));
val _ = \<^assert> (Thm.nprems_of @{thm LF.foo7'} = 3);
val _ = \<^assert> (is_some (induct_entry Induct.find_casesT \<^context> \<^typ>\<open>LF.T\<close> @{thm LF.r'}));
val _ = \<^assert> (diff_K 1 (@{thm LF.ipc}, H2 "ipc"));
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fa7} = 1 andalso one_light @{thm LF.fa7});
\<close>
(* theory level: lemma (in LF) fa6 [OF ax] reports Undefined fact *)
ML_val \<open>
val _ = \<^assert>
  ((lemma_in "LF" (Binding.name "fa6") "[OF ax]" "Pc S y \<Longrightarrow> Pc S y" (fn ctxt => assume_tac ctxt) \<^theory>; false)
    handle ERROR msg => String.isPrefix "Undefined fact" (Protocol_Message.clean_output msg));
\<close>
(* the theory-level goal without predicate facts does not close by simp *)
ML_val \<open>
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>gc (hc 0) = 0\<close>));
val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>LF.Leaf \<noteq> LF.Node a b\<close>));
\<close>

(* second version: facts unrelated to the block are stored as the theorems themselves, K 0 --
   one premise fewer than the twin's theory copy, two in the nested assumes blocks *)
ML_val \<open>
val _ = List.app (fn (n, delta) =>
    \<^assert> (Thm.nprems_of (LF_copy n) = Thm.nprems_of (D_copy n) + delta andalso
      not (has_K_tag (LF_copy n))))
  [("cj", ~1), ("hm", ~1)];
\<close>
ML_val \<open>
val _ = List.app (fn (n, delta) =>
    \<^assert> (Thm.nprems_of (LF_copy n) = Thm.nprems_of (D_copy n) + delta andalso
      not (has_K_tag (LF_copy n))))
  [("hle", ~2), ("h7", ~2)];
\<close>
ML_val \<open>\<^assert> (Thm.eq_thm_prop (@{thm LF.cj}, @{thm conjI}) andalso not (has_K_tag @{thm LF.cj}))\<close>
ML_val \<open>\<^assert> (Thm.eq_thm_prop (@{thm LF.hm}, @{thm monoid.r_one}) andalso not (has_K_tag @{thm LF.hm}))\<close>
ML_val \<open>\<^assert> (Thm.nprems_of @{thm LF.hle} = 2 andalso not (has_K_tag @{thm LF.hle}))\<close>
(* the sort row: one premise left, ?'a::order unchanged *)
ML_val \<open>
val _ = \<^assert> (Thm.nprems_of @{thm LF.h7} = 1 andalso not (has_K_tag @{thm LF.h7}));
val _ =
  (case map (Term.strip_comb o HOLogic.dest_Trueprop) (Thm.prems_of @{thm LF.h7}) of
    [(_, [Var (_, T), _])] => \<^assert> (case T of TVar (_, S) => S = \<^sort>\<open>order\<close> | _ => false)
  | _ => raise Fail "h7 shape");
\<close>
(* the tags of h5 and h5': both carry LF.foo's case names a b and consumes 2 (h5' is LF.foo
   itself, h5 adds the same case names) *)
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.h5} = 1 andalso
  AList.lookup (op =) (Thm.get_tags @{thm LF.h5}) "consumes" = SOME "2" andalso Rule_Cases.get_consumes @{thm LF.h5} = 2);
\<close>
ML_val \<open>\<^assert> (Rule_Cases.get @{thm LF.h5} = Rule_Cases.get @{thm LF.foo})\<close>
ML_val \<open>
val _ = \<^assert> (AList.lookup (op =) (Thm.get_tags @{thm LF.h5'}) "consumes" = SOME "2" andalso
  AList.defined (op =) (Thm.get_tags @{thm LF.h5'}) "case_names" andalso
  Exported_Premises.count_of @{thm LF.h5'} = 1 andalso Rule_Cases.get_consumes @{thm LF.h5'} = 2);
\<close>
(* the theory-level table entry of declare LF.foo[cases pred: Rc] is LF.foo itself *)
ML_val \<open>
val e = the (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Rc x S\<close> @{thm LF.foo});
val _ = \<^assert> (Rule_Cases.get e = Rule_Cases.get @{thm LF.foo} andalso Exported_Premises.count_of e = 1);
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm_prop (@{thm LF.r'}, @{thm LF.Abs_T_cases}) andalso
  Rule_Cases.get @{thm LF.r'} = Rule_Cases.get @{thm LF.Abs_T_cases} andalso Exported_Premises.count_of @{thm LF.r'} = 1);
\<close>


section \<open>The attribute steps keep K (N30)\<close>

(* unfolded, folded and rule_format end with keep_count (second version): the leading premises
   stay in front.  cst is an unconditional theory-level definition: the block's bar_def is
   shadowed by LF.bar_def, which is conditional, and the rewriter leaves a conditional rule
   unused *)
definition cst :: nat where "cst = 2"
context LF begin
lemma fub: "cst = cst" by (rule refl)
end
context LF begin
lemmas u = LF.fub[unfolded cst_def]
lemmas uf = u[folded cst_def]
lemmas uL = LF.fub[unfolded LF_def]
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm u} = 1)\<close>
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm uf} = 1)\<close>
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm uL}, Logic.varify_global \<^prop>\<open>UP_cring (S :: ('a, 'b) ring_scheme) \<Longrightarrow> cst = cst\<close>)
  andalso Exported_Premises.count_of @{thm uL} = 1);
\<close>
end
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.u} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (2::nat) = 2\<close>
  andalso Exported_Premises.count_of @{thm LF.u} = 1);
\<close>
ML_val \<open>
val _ = \<^assert> (Thm.prop_of @{thm LF.uf} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> cst = cst\<close>
  andalso Exported_Premises.count_of @{thm LF.uf} = 1);
\<close>
ML_val \<open>
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.uL}, Logic.varify_global \<^prop>\<open>UP_cring (S :: ('a, 'b) ring_scheme) \<Longrightarrow> cst = cst\<close>)
  andalso Exported_Premises.count_of @{thm LF.uL} = 1);
\<close>
(* the direct rows: each rewriting row also checks that the rewriting happened *)
ML_val \<open>
val inp = Exported_Premises.put 1 @{thm LF.fub};
val out = Local_Defs.unfold \<^context> @{thms cst_def} inp;
val _ = \<^assert> (not (Thm.prop_of out aconv Thm.prop_of inp));
val _ = \<^assert> (Exported_Premises.count_of out = 1 andalso
  Thm.prop_of out aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (2::nat) = 2\<close>);
\<close>
ML_val \<open>
val inp = Exported_Premises.put 1 @{thm LF.u};
val out = Local_Defs.fold \<^context> @{thms cst_def} inp;
val _ = \<^assert> (not (Thm.prop_of out aconv Thm.prop_of inp));
val _ = \<^assert> (Exported_Premises.count_of out = 1 andalso
  Thm.prop_of out aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> cst = cst\<close>);
\<close>
ML_val \<open>
val out = Object_Logic.rulify \<^context> @{thm LF.fr0};
val _ = \<^assert> (Exported_Premises.count_of out = 1 andalso Thm.nprems_of out = 2);
\<close>
(* the recorded limitation (plan section 3.5 (b)): an equation whose left-hand side is an
   implication merges leading premises, and K is copied as it is *)
ML_val \<open>
val out = Local_Defs.unfold \<^context> @{thms atomize_conjL} @{thm LF.foo};
val _ = \<^assert> (Thm.nprems_of out = 1 andalso Exported_Premises.count_of out = 1);
\<close>

end
