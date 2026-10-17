(* Test support for Light_Locale_Test (plan section 7, preface).
   with_warnings ("rows that assert a warning") runs a thunk and returns its result together with
   the warnings it emitted on this thread.  A forwarding wrapper is installed once on
   Private_Output.warning_fn: it always forwards to the original function (the build log is
   unchanged) and, when this thread has a buffer set, also appends each message's YXML content to
   it.  This theory must not go into the Light_Locale_Base heap: isabelle_process.ML:133-134
   reinstalls warning_fn at process start.
   light_locale_cmd/locale_cmd drive the exported entry points Expression.add_light_locale_cmd and
   Expression.add_locale_cmd on header text, for the negative rows ("every negative assertion names
   the exported entry function").  The theory imports only Light_Locale, so that a leaf may declare
   its own fixtures under the names the plan uses. *)
theory Test_Support
  imports "Light_Locale.Light_Locale"
begin

ML \<open>
signature TEST_SUPPORT =
sig
  val with_warnings: (unit -> 'a) -> 'a * string list
  val light_locale_cmd: string -> theory -> string * local_theory
  val locale_cmd: string -> theory -> string * local_theory
  val light: theory -> string -> unit -> string * local_theory
  val heavy: theory -> string -> unit -> string * local_theory
  val fails_checked: string -> (string -> bool) -> (unit -> 'a) -> unit
  val fails_with: string -> (unit -> 'a) -> unit
  val fails_prefix: string -> (unit -> 'a) -> unit
  val accepted: (unit -> string * local_theory) -> (string * theory) * string list
  val rejected: string -> (unit -> 'a) -> string list
  val eliminated_name_warning: string -> string -> string
  val defined_as: string -> string -> string -> string -> string
  val loc: theory -> string -> string
  val params: theory -> string -> (string * typ * bool) list
  val edge: theory -> string -> string -> morphism
  val instances: theory -> string -> string -> term list
  val tfrees: term list -> (string * sort) list
  val extra_hyps: Proof.context -> string -> term list
  val facts_under: theory -> string -> string list
  val visible_fact_names: Proof.context -> string list
  val has_fact: Proof.context -> string -> bool
  val bundle_of: Proof.context -> string -> (thm list * Token.src list) list
  val consts_named: Proof.context -> string -> string list
  val marks_of: Proof.context -> string -> term list -> (term list * Locale.level * string list) list
  val marks_are: Proof.context -> string -> term list -> (term list * Locale.level * string list) list -> bool
  val registration_prefixes: Proof.context -> string -> (string * bool) list list
  val rhs_of: Proof.context -> string -> term
  val interpretation_cmd: string -> theory -> theory
  val attribs_of: theory -> string -> Token.src list
  val theorem_in: local_theory -> binding -> string -> string -> (Proof.context -> int -> tactic) -> local_theory
  val lemma_in: string -> binding -> string -> string -> (Proof.context -> int -> tactic) -> theory -> theory
  val declare_in: local_theory -> string -> string -> local_theory
  val twin_rename: string * string -> term -> term
  val assert_twin: theory -> string * string -> unit
  val lemmas_in: local_theory -> string -> string -> string -> thm list * local_theory
  val thy_ctxt: Proof.context -> Proof.context
  val proves: (Proof.context -> tactic) -> Proof.context -> term -> bool
  val by_simp: Proof.context -> term -> bool
  val by_auto: Proof.context -> term -> bool
  val by_blast: Proof.context -> term -> bool
  val has_K_tag: thm -> bool
  val tags_without_K: thm -> Properties.T
  val light_prems: Proof.context -> thm -> term list
  val simp_props: Proof.context -> term list
  val plain_equal: thm * thm -> bool
  val three_items: thm * thm -> bool
  val diff_K: int -> thm * thm -> bool
  val twin_names: string * string -> term -> term
  val varify_block: term -> term
  val block_lemma: string * string -> int -> thm * thm -> bool
  val phi: string -> thm -> term
  val canonical_vars: term -> term
  val canonical_tvars: term -> term
  val same_shape: term * term -> bool
  val phi_equal: string * string -> thm * thm -> bool
  val major_is: string -> thm -> bool
  val major_prem_is: Proof.context -> string -> thm -> bool
  val proof_after_goals: {apply: bool} -> Proof.context -> thm list -> string -> term list -> Proof.state
  val proof_after: {apply: bool} -> Proof.context -> thm list -> string -> term -> Proof.state
  val run_goals: Proof.context -> thm list -> string -> string list -> Proof.state
  val run: Proof.context -> thm list -> string -> string -> Proof.state
  val run_apply: Proof.context -> thm list -> string -> string -> Proof.state
  val by_method: Proof.context -> thm list -> string -> string -> bool
  val canonical_text: string -> string
  val cases_text: Proof.state -> string list
  val case_names: Proof.state -> string list
  val counts: Proof.state -> int list
  val cases_terms: (term -> term) -> Proof.state ->
    (string * (string * typ) list * (string * term list) list * (indexname * term option) list) list
  val goal_prems: Proof.state -> term list
  val subgoals: Proof.state -> int
  val fix_in: Proof.context -> (string * typ) list -> Proof.context
  val assume_in: Proof.context -> (string * typ) list -> string -> string -> thm * Proof.context
  val note_in: Proof.context -> string -> string -> thm -> thm * Proof.context
  val induct_entry: (Proof.context -> 'a -> thm list) -> Proof.context -> 'a -> thm -> thm option
  val claset_entries: Proof.context -> thm -> (thm * thm * Bires.kind) list
  val claset_rule: Proof.context -> Bires.kind -> thm -> thm * thm
  val tokens: theory -> string -> Token.T list
  val declares: theory -> string -> string list
  val blast_warns: Proof.context -> string -> bool * bool
  val cla_modified: Proof.context -> string -> Proof.context
  val clean: string -> string
  val layers: Proof.context -> string option * term option
  val implicit_is: Proof.context -> term -> bool
  val shows: Proof.context -> term -> string
  val reads: Proof.context -> string -> term
  val prints_as: Proof.context -> string -> string -> unit
  val round_trips: Proof.context -> term -> bool
  val golden_line: theory -> string -> string -> string
  val parse_text: 'a parser -> theory -> string -> 'a
  val assumes_of: theory -> string -> (string * term list) list
  val attribute_terms: theory -> string -> (string * term list) list
  val after_elimination: theory -> string -> string list -> term -> term
  val assumes_equal: (theory -> string -> (string * term list) list) ->
    theory -> string * string -> string list -> bool
  val params_equal: theory -> string * string -> string list -> bool
  val has_placeholder: term -> bool
  val placeholder_fixed: Proof.context -> bool
  val bare_denotes: Proof.context -> string -> bool
  val has_bad_markup: Proof.context -> term -> bool
  val locale_expression: theory -> string -> Expression.expression
end;

structure Test_Support: TEST_SUPPORT =
struct

val buffer: string list Unsynchronized.ref Thread_Data.var = Thread_Data.var ();

val _ =
  let val original = ! Private_Output.warning_fn in
    Private_Output.warning_fn :=
      (fn ss =>
        ((case Thread_Data.get buffer of
            SOME buf => Unsynchronized.change buf (cons (Protocol_Message.clean_output (implode ss)))
          | NONE => ());
         original ss))
  end;

fun with_warnings f =
  let
    val buf = Unsynchronized.ref [];
    val result = Thread_Data.setmp buffer (SOME buf) f ();
  in (result, rev (! buf)) end;

(*the proper tokens of a text, by the theory's keywords*)
fun tokens thy text = filter Token.is_proper (Token.explode (Thy_Header.get_keywords thy) Position.none text);

(*the text after the command word: "name = expression + elements"*)
fun gen_locale_cmd add text thy =
  let
    val toks = tokens thy text;
    val parser =
      Parse.binding --
        Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse_Spec.locale_val) ((([], []), []), []);
    val (name, ((expr, includes), elems)) =
      #1 (Scan.finite Token.stopper (Parse.!!! (parser --| Scan.ahead Parse.eof)) toks);
  in add name Binding.empty includes expr elems thy end;

val light_locale_cmd = gen_locale_cmd Expression.add_light_locale_cmd;
val locale_cmd = gen_locale_cmd Expression.add_locale_cmd;
fun light thy text = fn () => light_locale_cmd text thy;
fun heavy thy text = fn () => locale_cmd text thy;

(*the declaration must fail with exactly this message / a message with this prefix (plan section 7
  preface: a checker that compares the text cannot pass on an accepted declaration -- the
  "accepted" sentinel is raised outside the handler)*)
(*the ERROR, also when a parallel evaluation (Syntax.read_terms of a header's instances) wrapped
  it into EXCEPTIONS*)
fun error_message (ERROR msg) = SOME msg
  | error_message (Exn.EXCEPTIONS exns) = get_first error_message exns
  | error_message exn =
      (case Par_Exn.dest exn of SOME exns => get_first error_message exns | NONE => NONE);
fun fails_checked describe check f =
  (case Exn.capture f () of
    Exn.Res _ => error "accepted"
  | Exn.Exn exn =>
      (case error_message exn of
        SOME msg =>
          let val got = Protocol_Message.clean_output msg
          in if check got then () else error ("got:\n" ^ got ^ "\nexpected " ^ describe) end
      | NONE => Exn.reraise exn));
fun fails_with expected = fails_checked (":\n" ^ expected) (fn got => got = expected);
fun fails_prefix expected = fails_checked ("prefix:\n" ^ expected) (String.isPrefix expected);

(*the section 6 message of the defined position (test 8)*)
fun defined_as ord y loc shown =
  "The " ^ ord ^ " parameter `" ^ y ^ "` of locale `" ^ loc ^ "` is defined as `" ^ shown ^
    "` and cannot be instantiated. You must write `_`.";

(*locales by name: the parameter table (name, type, whether the mixfix is NoSyn), the morphism of
  the edge from parent p to l (plan line 4966) and the instances of p's parameters under it*)
fun loc thy n = Locale.check_global thy (n, Position.none);
fun params thy l = map (fn ((x, T), mx) => (x, T, Mixfix.equal (mx, NoSyn))) (Locale.params_of thy l);
fun edge thy p l =
  the (find_first (fn {source, target, ...} => source = loc thy p andalso target = loc thy l)
    (Locale.dest_dependencies [] thy)) |> #morphism;
fun instances thy p l = Locale.instance_of thy (loc thy p) (edge thy p l);
fun tfrees ts = fold Term.add_tfrees ts [];


(*the full names of the theory facts with the given prefix*)
fun facts_under thy prefix =
  Facts.dest_static false [] (Global_Theory.facts_of thy)
  |> map #1 |> filter (String.isPrefix prefix) |> sort_strings;

(*the names of the facts visible in the context, the theory's own included*)
fun visible_fact_names ctxt =
  Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
    (Proof_Context.facts_of ctxt)
  |> map #1 |> sort_strings;

(*whether the fact name resolves in the context*)
fun has_fact ctxt name = can (Proof_Context.get_fact ctxt) (Facts.named name);

(*the entries of a bundle, by its name (bundle.ML: get takes the internal name check returns)*)
fun bundle_of ctxt name = Bundle.get ctxt (Bundle.check ctxt (name, Position.none));

(*the constants of the context (global and local) with the given base name*)
fun consts_named ctxt base =
  #constants (Consts.dest (Proof_Context.consts_of ctxt))
  |> map #1 |> filter (fn c => Long_Name.base_name c = base) |> sort_strings;

(*the recorded marks matching an instance of the locale (plan section 7, preface)*)
fun marks_of ctxt loc insts =
  Locale.matching_marks_of (Context.Proof ctxt) (Locale.check ctxt (loc, Position.none), insts);

(*the recorded marks are exactly the expected ones, as a multiset: the plan fixes neither the order
  of the records (table insertion) nor the order of an effect list (a union)*)
fun marks_are ctxt loc insts expected =
  let
    fun norm recs =
      map (fn (ts, level, effects) => (ts, level, sort_strings effects)) recs
      |> sort (list_ord Term_Ord.term_ord o apply2 #1);
  in norm (marks_of ctxt loc insts) = norm expected end;

(*the binding prefixes of the registrations of the locale, in table order*)
fun registration_prefixes ctxt loc =
  Locale.registrations_of (Context.Proof ctxt) (Locale.check ctxt (loc, Position.none))
  |> map (fn (_, m) => Morphism.binding_prefix m);

(*the right-hand side of an abbreviation, by its full name*)
fun rhs_of ctxt c =
  the (#2 (the (AList.lookup (op =) (#constants (Consts.dest (Proof_Context.consts_of ctxt))) c)));

(*the whole text through a parser: "[simp, symmetric]", a locale expression, and the like*)
fun parse_text p thy text =
  let val toks = tokens thy text
  in #1 (Scan.finite Token.stopper (Parse.!!! (p --| Scan.ahead Parse.eof)) toks) end;

val locale_expression = parse_text Parse_Spec.locale_expression;

(*the text after the command word; the obligations are closed by unfold_locales and simp*)
fun interpretation_cmd text thy =
  let
    val expr = locale_expression thy text;
    fun meth ctxt =
      Method.SIMPLE_METHOD
        (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN ALLGOALS (asm_full_simp_tac ctxt));
  in
    Named_Target.theory_init thy
    |> Interpretation.isar_interpretation_cmd expr
    |> Proof.global_terminal_proof ((Method.Basic meth, Position.no_range), NONE)
    |> Local_Theory.exit_global
  end;

fun attribs_of thy text = parse_text Parse.attribs thy text;

(*lemma <binding> <attribs>: <statement> by (<tac>), driven through Specification.theorem_cmd*)
fun theorem_in lthy binding atts stmt tac =
  lthy
  |> Specification.theorem_cmd true Thm.theoremK NONE (K I)
      (binding, attribs_of (Proof_Context.theory_of lthy) atts) [] []
      (Element.Shows [(Binding.empty_atts, [(stmt, [])])]) false
  |> Proof.global_terminal_proof
      ((Method.Basic (fn ctxt => Method.SIMPLE_METHOD (ALLGOALS (tac ctxt))), Position.no_range), NONE);

(*lemma (in <locale>) ...*)
fun lemma_in loc binding atts stmt tac thy =
  Named_Target.init [] (Locale.check_global thy (loc, Position.none)) thy
  |> (fn lthy => theorem_in lthy binding atts stmt tac)
  |> Local_Theory.exit_global;

(*<binding> = <thms> <attribs>, as the command of the kind (declare: "", lemmas: Thm.theoremK)*)
fun theorems_in kind lthy binding thms atts =
  let val thy = Proof_Context.theory_of lthy in
    Specification.theorems_cmd kind
      [(binding, [parse_text Parse.thms1 thy thms |> hd |> apsnd (K (attribs_of thy atts))])] [] false lthy
  end;

(*declare <thms> <attribs>*)
fun declare_in lthy thms atts = #2 (theorems_in "" lthy Binding.empty_atts thms atts);

(*lemmas <name> = <thms> <attribs>, returning the facts the command gives back*)
fun lemmas_in lthy name thms atts =
  theorems_in Thm.theoremK lthy (Binding.name name, []) thms atts |>> maps #2;

val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;

(*the forcing thunk of the preface: the tactic run to completion by Goal.prove*)
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_simp = proves (fn ctxt => asm_full_simp_tac ctxt 1);  (*the simp method's default tactic*)
val by_auto = proves auto_tac;
val by_blast = proves (fn ctxt => blast_tac ctxt 1);

(*the hyps of a fact that are not assumptions of the context*)
fun extra_hyps ctxt name =
  let val assms = map Thm.term_of (Assumption.all_assms_of ctxt) in
    Proof_Context.get_fact ctxt (Facts.named name)
    |> maps Thm.hyps_of |> filter_out (member (op aconv) assms)
  end;


(* the twin projection (plan section 7, preface): each locale has its own predicate constants, so
   the light locale's are renamed to the heavy twin's before comparing *)

fun twin_rename (l, h) =
  let val renaming = [(l, h), (l ^ "_axioms", h ^ "_axioms")] in
    Term.map_aterms
      (fn Const (c, T) => Const (the_default c (AList.lookup (op =) renaming c), T) | t => t)
  end;

(*the assumptions a locale records, by binding name: every proposition (assumes_of), or the terms
  their attributes read once and keep in their tokens, as Args.term does (attribute_terms); a
  heavy twin's term after elimination -- the parameters the twin's block defines (its x_def
  facts) replaced by their definitions, the elimination step of the twin projection (plan section
  7 preface; none defined = the ordinary twin); the projections test 9's header rows and
  assert_twin share: the assumptions (names and one of the two term lists, the light side
  renamed) and the parameters (name, type, mixfix) without the twin's defined ones*)
fun assumes_elements thy name =
  maps (fn Element.Assumes asms => asms | _ => []) (Locale.hyp_spec_of thy name);
fun assumes_of thy name =
  map (fn ((b, _), props) => (Binding.name_of b, map #1 props)) (assumes_elements thy name);
fun attribute_terms thy name =
  let
    fun term_value tok = (case Token.get_value tok of SOME (Token.Term t) => SOME t | _ => NONE);
    val terms = maps (map_filter term_value o Token.args_of_src);
  in map (fn ((b, srcs), _) => (Binding.name_of b, terms srcs)) (assumes_elements thy name) end;
fun after_elimination thy twin defined =
  if null defined then I
  else
    let
      val ctxt = Locale.init (loc thy twin) thy;
      val env =
        map (fn x => Logic.dest_equals (Thm.prop_of (Proof_Context.get_thm ctxt (x ^ "_def")))) defined;
    in Term.subst_atomic env end;
fun assumes_equal project thy (l, h) defined =
  eq_list (fn ((n, ps), (n', ps')) => n = n' andalso eq_list (op aconv) (map (twin_rename (l, h)) ps, ps'))
    (project thy l, map (apsnd (map (after_elimination thy h defined))) (project thy h));
fun params_equal thy (l, h) defined =
  eq_list (fn (((x, T), mx), ((x', T'), mx')) => x = x' andalso T = T' andalso Mixfix.equal (mx, mx'))
    (Locale.params_of thy l, filter_out (member (op =) defined o #1 o #1) (Locale.params_of thy h));

fun assert_twin thy (l, h) =
  let
    fun check what b = if b then () else error ("Twin projection fails: " ^ what);
    val prems_equal = eq_list (op aconv);
    fun thms_equal (thl, thh) =
      prems_equal (map (twin_rename (l, h)) (Thm.prems_of thl), Thm.prems_of thh);

    val _ = check "params_of" (params_equal thy (l, h) []);

    val (al, bl) = Locale.specification_of thy l and (ah, bh) = Locale.specification_of thy h;
    val _ = check "specification_of, #2" (bl = bh);
    val _ = check "specification_of, #1"
      (case (al, ah) of
        (NONE, NONE) => true
      | (SOME tl, SOME th) =>
          (case apply2 (Term.strip_comb o HOLogic.dest_Trueprop) (tl, th) of
            ((Const (cl, _), xl), (Const (ch, _), xh)) => cl = l andalso ch = h andalso xl = xh
          | _ => false)
      | _ => false);

    val (il, il') = Locale.intros_of thy l and (ih, ih') = Locale.intros_of thy h;
    fun intro_equal (NONE, NONE) = true
      | intro_equal (SOME thl, SOME thh) = thms_equal (thl, thh)
      | intro_equal _ = false;
    val _ = check "intros_of" (intro_equal (il, ih) andalso intro_equal (il', ih'));

    val xl = Locale.axioms_of thy l and xh = Locale.axioms_of thy h;
    val _ = check "axioms_of"
      (eq_list (fn (thl, thh) =>
          thms_equal (thl, thh) andalso twin_rename (l, h) (Thm.prop_of thl) = Thm.prop_of thh)
        (xl, xh));

    val _ = check "hyp_spec_of" (assumes_equal assumes_of thy (l, h) []);
  in () end;


(* the comparisons of plan section 7 test 6 (preface: "normal equality" of local copies, the three
   items, "Rule_Cases.get equal up to K", the normalisation phi, the table checks) *)

fun has_K_tag th = AList.defined (op =) (Thm.get_tags th) Exported_Premises.exported_premises_tagN;

(*the tags other than K; Thm.untag_rule, not Exported_Premises.put, which is under test*)
fun tags_without_K th = Thm.get_tags (Thm.untag_rule Exported_Premises.exported_premises_tagN th);

fun light_prems ctxt th = filter (Light_Locale_Axiom_Facts.is_light_prop ctxt) (Thm.prems_of th);

(*the statements of the context's simp rules*)
fun simp_props ctxt = map (Thm.prop_of o #2) (Raw_Simplifier.dest_simps (simpset_of ctxt));

(*"Rule_Cases.get equal up to K", K being the count the row states: the light theorem carries
  exactly that count, the case names agree, consumes differ by it*)
fun diff_K k (thl, thh) =
  let val (il, nl) = Rule_Cases.get thl and (ih, nh) = Rule_Cases.get thh
  in Exported_Premises.count_of thl = k andalso il = ih andalso nl = nh + k end;

(*a local copy whose statement names neither the predicate nor a block constant*)
fun plain_equal (thl, thh) =
  Thm.eq_thm_prop (thl, thh) andalso diff_K 0 (thl, thh) andalso not (has_K_tag thl);

(*any other local copy*)
fun three_items (thl, thh) = Thm.nprems_of thl = Thm.nprems_of thh andalso diff_K 0 (thl, thh);

(*rename the name segment l to h in every constant and type name: the predicate, its _axioms, and
  the constants and types declared in the block (Thy.LF.f, Thy.LF.tr)*)
fun twin_names (l, h) =
  let
    fun segment s = if s = l then h else if s = l ^ "_axioms" then h ^ "_axioms" else s;
    val rename = Long_Name.implode o map segment o Long_Name.explode;
    fun renameT (Type (c, Ts)) = Type (rename c, map renameT Ts)
      | renameT T = T;
  in
    Term.map_aterms (fn Const (c, T) => Const (rename c, T) | t => t)
    #> Term.map_types renameT
  end;

(*a heavy block fact's statement with the block's fixed variables and type variables as index-0
  Vars and TVars (Logic.varify_global rejects a term that already has schematic variables)*)
val varify_block =
  Term.map_aterms (fn Free (x, T) => Var ((x, 0), T) | t => t)
  #> Term.map_types (Term.map_atyps (fn TFree (a, S) => TVar ((a, 0), S) | T => T));

(*the theory copy of a lemma proved in the block against the heavy block fact: (i) the statement
  without the K exported premises, (ii) the premise count, (iii) Rule_Cases up to K*)
fun block_lemma (l, h) k (thl, thh) =
  let
    val prop = Thm.prop_of thl;
    val stmt = Logic.list_implies (drop k (Logic.strip_imp_prems prop), Logic.strip_imp_concl prop);
  in
    twin_names (l, h) stmt aconv varify_block (Thm.prop_of thh) andalso
    Thm.nprems_of thl = Thm.nprems_of thh + k andalso
    diff_K k (thl, thh)
  end;

(*phi: the one premise led by the locale's predicate constant is removed and its variable
  arguments are instantiated positionally by the same Frees on both sides*)
fun phi pred th =
  let
    val prop = Thm.prop_of th;
    fun pred_args t =
      (case Term.strip_comb (HOLogic.dest_Trueprop t) of
        (Const (c, _), args) => if c = pred then SOME args else NONE
      | _ => NONE) handle TERM _ => NONE;
    val (args, rest) =
      (case List.partition (is_some o pred_args) (Logic.strip_imp_prems prop) of
        ([p], rest) => (the (pred_args p), rest)
      | _ => raise THM ("phi: not exactly one predicate premise", 0, [th]));
    val inst =
      map_index (fn (i, Var (v, T)) => (v, Free ("p" ^ string_of_int i, T))
        | (_, t) => raise TERM ("phi: predicate argument is not a variable", [t])) args;
  in
    Logic.list_implies (rest, Logic.strip_imp_concl prop)
    |> Term.map_aterms (fn t as Var (v, _) => the_default t (AList.lookup (op =) inst v) | t => t)
  end;

(*schematic variables renamed by order of occurrence: the heavy twin D fixes P, so its package
  rules say ?Pa where the light ones say ?P*)
fun canonical_vars t =
  let val inst = map_index (fn (i, (v, T)) => ((v, T), Var (("v", i), T))) (rev (Term.add_vars t []))
  in Term.map_aterms (fn Var v => the (AList.lookup (op =) inst v) | t => t) t end;

(*type variables likewise; the two together: alpha-equivalence of statements*)
fun canonical_tvars t =
  let
    val inst = map_index (fn (i, (v, S)) => ((v, S), TVar (("'v", i), S))) (rev (Term.add_tvars t []))
  in Term.map_types (Term.map_atyps (fn TVar v => the (AList.lookup (op =) inst v) | T => T)) t end;

fun same_shape (t, u) =
  let val canonical = canonical_tvars o canonical_vars
  in canonical t aconv canonical u end;

fun phi_equal (lpred, hpred) (thl, thh) =
  canonical_vars (twin_names (Long_Name.base_name lpred, Long_Name.base_name hpred) (phi lpred thl))
    aconv canonical_vars (phi hpred thh);

(*the major premise is the constant applied to variables only*)
fun major_is c th =
  (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of th)) of
    (Const (c', _), args) => c' = c andalso forall is_Var args
  | _ => false) handle TERM _ => false;

(*the major premise is the literal term, up to renaming of its variables*)
fun major_prem_is ctxt text th =
  same_shape (Thm.major_prem_of th, Logic.varify_global (Syntax.read_prop ctxt text));

(* driving Isar proofs programmatically (test 6, the Rule_Cases rows): the state after
   "lemma goals using facts proof (method)" -- or "apply (method)" -- whose context is read for
   its cases; the facts are given as theorems, the method as text, the goals as terms (one per
   "and" group) or, for run and run_apply, as the text of one goal *)

fun proof_after_goals {apply} ctxt facts method goals =
  let
    val (text, _) = Method.read_closure_input ctxt (Input.string method);
    val state =
      Proof.theorem NONE (K I) (map (fn goal => [(goal, [])]) goals) ctxt |> Proof.using [[(facts, [])]];
    val results =
      if apply then Proof.apply (text, Position.no_range) state
      else Proof.proof (SOME (text, Position.no_range)) state;
  in Seq.the_result "proof_after" results end;

fun proof_after flags ctxt facts method goal = proof_after_goals flags ctxt facts method [goal];
fun run_goals ctxt facts method goals =
  proof_after_goals {apply = false} ctxt facts method (map (Syntax.read_prop ctxt) goals);
fun run ctxt facts method goal = run_goals ctxt facts method [goal];
fun run_apply ctxt facts method goal = proof_after {apply = true} ctxt facts method (Syntax.read_prop ctxt goal);

(*whether `from <facts> show <goal> by <method>` succeeds: the terminal proof backtracks over the
  method's results until one finishes (".." is by standard)*)
fun by_method ctxt facts method goal =
  let val (text, _) = Method.read_closure_input ctxt (Input.string method) in
    can (fn () =>
      Proof.theorem NONE (K I) [[(Syntax.read_prop ctxt goal, [])]] ctxt
      |> Proof.using [[(facts, [])]]
      |> Proof.global_terminal_proof ((text, Position.no_range), NONE)) ()
  end;

(*what print_cases prints, without markup or line layout, the schematic variables renamed by
  order of first occurrence: the heavy twin D fixes P, so its rules say ?Pa where the light ones
  say ?P*)
fun canonical_text s =
  let
    fun scan [] _ acc = implode (rev acc)
      | scan ("?" :: rest) tab acc =
          let
            val (name, rest') = chop_prefix (fn c => Symbol.is_letdig c orelse c = "'" orelse c = "_") rest;
            val key = implode name;
            val (idx, tab') =
              (case AList.lookup (op =) tab key of
                SOME i => (i, tab)
              | NONE => (length tab, (key, length tab) :: tab));
          in scan rest' tab' (rev (Symbol.explode ("?v" ^ string_of_int idx)) @ acc) end
      | scan (c :: rest) tab acc = scan rest tab (c :: acc);
  in scan (Symbol.explode s) [] [] end;

fun cases_text st =
  map (canonical_text o Protocol_Message.clean_output o Pretty.unformatted_string_of)
    (Proof_Context.pretty_cases (Proof.context_of st));

fun dest_cases st = Proof_Context.dest_cases NONE (Proof.context_of st);

fun case_names st = map #1 (dest_cases st);

(*the number of assumptions of each case*)
fun counts st = map (fn (_, Rule_Cases.Case {assumes, ...}) => length (maps #2 assumes)) (dest_cases st);

(*each case's name, fixes, assumption groups and binds, with f applied to every term*)
fun cases_terms f st =
  dest_cases st |> map (fn (name, Rule_Cases.Case {fixes, assumes, binds, ...}) =>
    (name, map (apfst Binding.name_of) fixes, map (apsnd (map f)) assumes, map (apsnd (Option.map f)) binds));

fun goal_prems st = Thm.prems_of (#goal (Proof.goal st));
val subgoals = length o goal_prems;

(*a context with the variables fixed*)
fun fix_in ctxt fixes =
  #2 (Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes) ctxt);

(*a context with the variables fixed and the assumption name: prop, read there*)
fun assume_in ctxt fixes name prop =
  let
    val ctxt' = fix_in ctxt fixes;
    val ([(_, [th])], ctxt'') =
      Proof_Context.add_assms Assumption.assume_export
        [((Binding.name name, []), [(Syntax.read_prop ctxt' prop, [])])] ctxt';
  in (th, ctxt'') end;

(*note <name> [<attribs>] = th in the context*)
fun note_in ctxt name atts th =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ([(_, [th'])], ctxt') =
      Proof_Context.note_thmss ""
        [((Binding.name name, map (Attrib.attribute_cmd ctxt) (attribs_of thy atts)), [([th], [])])] ctxt;
  in (th', ctxt') end;

(*the Induct table entry Thm.eq_thm_prop with the theorem, if any*)
fun induct_entry find ctxt key th = find_first (fn r => Thm.eq_thm_prop (r, th)) (find ctxt key);

(*the claset entries whose key is Thm.eq_thm_prop with the theorem: key, derived plain rule, kind*)
fun claset_entries ctxt th =
  Classical.dest_decls ctxt (fn (key, _) => Thm.eq_thm_prop (key, th))
  |> map (fn (key, {kind, info = {plain, ...}, ...}) => (key, plain, kind));

(*the one entry of the kind: key and derived plain rule*)
fun claset_rule ctxt kind th =
  the_single (map_filter (fn (key, plain, k) => if k = kind then SOME (key, plain) else NONE)
    (claset_entries ctxt th));

(*the warnings a light_locale declaration emits*)
fun declares thy text = #2 (with_warnings (fn () => light_locale_cmd text thy));

(*a declaration that succeeds: its name in the theory holding it, with its warnings; one that
  fails with the given error: its warnings*)
fun accepted f = let val ((name, lthy), ws) = with_warnings f in ((name, Proof_Context.theory_of lthy), ws) end;
fun rejected msg f = #2 (with_warnings (fn () => fails_with msg f));

(*the D20 use warning as Locale.eliminated_name_warning prints it*)
fun eliminated_name_warning x loc =
  "The parameter `" ^ x ^ "` from locale `" ^ loc ^ "` is not bound any more and treated as a fresh variable here.";

(*whether blast closes the goal, and whether it warned "Ignoring weak elimination rule"*)
fun blast_warns ctxt goal =
  let val (ok, ws) = with_warnings (fn () => by_blast ctxt (Syntax.read_prop ctxt goal))
  in (ok, exists (String.isPrefix "Ignoring weak elimination rule") ws) end;

(*the proof context after the classical modifiers intro:/elim:/dest:/del: of a method call, read
  through the method's own argument parser (method.ML method_syntax); a modifier's effect lasts for
  the call, so this is how a leaf reads it*)
fun cla_modified ctxt text =
  #2 (Token.syntax (Method.sections Classical.cla_modifiers)
    (Token.make_src ("cla_modified", Position.none) (tokens (Proof_Context.theory_of ctxt) text)) ctxt);

(*test 9: text without markup; the two structure layers of a context (the head of the variable
  structures, the implicit structure); the implicit structure up to types; what the printer
  prints in no print mode; a term read in a context; a text that reads and prints back as the
  expected text; the line of a golden file that follows a label and a tab*)
val clean = XML.content_of o YXML.parse_body;
fun layers ctxt = (Syntax_Trans.default_struct ctxt, Syntax_Trans.implicit_structure ctxt);
fun implicit_is ctxt t =
  (case Syntax_Trans.implicit_structure ctxt of SOME u => Term.aconv_untyped (u, t) | NONE => false);
fun shows ctxt t =
  clean (Print_Mode.setmp []
    (Pretty.string_of_ops (Pretty.output_ops (SOME 1000)) o Syntax.pretty_term ctxt) t);
fun reads ctxt text = Syntax.read_term ctxt text;
fun prints_as ctxt text expected =
  let val got = shows ctxt (reads ctxt text)
  in if got = expected then () else error ("printed:\n" ^ got ^ "\nexpected:\n" ^ expected) end;
(*the printed text of a term reads back as the term (in no print mode, at width 1000)*)
fun round_trips ctxt t = reads ctxt (shows ctxt t) aconv t;
fun golden_line thy name label =
  let
    val path = Path.appends [Resources.master_directory thy, Path.explode "../golden", Path.basic name];
    val prefix = label ^ "\t";
  in
    (case find_first (String.isPrefix prefix) (split_lines (File.read path)) of
      SOME line => unprefix prefix line
    | NONE => error ("no line " ^ quote label ^ " in golden " ^ name))
  end;

(*test 9: whether the placeholder of the implicit structure is left in a term; whether it is
  fixed exactly once under its literal name (no skolem variant); whether the bare operator, read
  with fresh names, is the operator of this structure; whether the printer marks anything bad in
  a term (symbolic output keeps the markup)*)
val has_placeholder =
  Term.exists_subterm (fn Free (x, _) => x = Syntax_Trans.implicit_structure_ | _ => false);
fun placeholder_fixed ctxt =
  filter (fn (x, _) => x = Syntax_Trans.implicit_structure_) (Variable.dest_fixes ctxt) =
    [(Syntax_Trans.implicit_structure_, Syntax_Trans.implicit_structure_)];
fun bare_denotes ctxt text =
  reads ctxt "a \<otimes> b" aconv reads ctxt ("a \<otimes>\<^bsub>" ^ text ^ "\<^esub> b");
fun has_bad_markup ctxt t =
  let
    fun bad (XML.Elem ((name, _), body)) = name = Markup.badN orelse exists bad body
      | bad (XML.Text _) = false;
  in exists bad (YXML.parse_body (Pretty.symbolic_string_of (Syntax.pretty_term ctxt t))) end;

end;
\<close>

(* a declaration attribute that does nothing, never fails and never warns: a bundle entry without an
   attribute source is dropped (attrib.ML:397), so the bundle rows of tests 6 and 7 carry [keep] *)
attribute_setup keep = \<open>Scan.succeed (Thm.declaration_attribute (K I))\<close>

(* self-check: a warning raised inside the thunk is captured, one outside it is not *)
ML \<open>
val ((), ws) = Test_Support.with_warnings (fn () => warning "test_support_probe");
val _ = \<^assert> (ws = ["test_support_probe"]);
val _ = warning "test_support_outside";
val ((), ws') = Test_Support.with_warnings (fn () => ());
val _ = \<^assert> (null ws');
\<close>

(* self-check: the declaration helpers succeed on a good header and fail on a bad one *)
ML \<open>
val _ = \<^assert> (can (Test_Support.light_locale_cmd "TS_ok = fixes a :: nat") \<^theory>);
val _ = \<^assert> (can (Test_Support.locale_cmd "TS_ok = fixes a :: nat") \<^theory>);
val _ = \<^assert> (not (can (Test_Support.locale_cmd "TS_bad = TS_no_such_locale") \<^theory>));
\<close>

end
