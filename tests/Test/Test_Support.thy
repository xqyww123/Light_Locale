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
  val extra_hyps: Proof.context -> string -> term list
  val facts_under: theory -> string -> string list
  val visible_fact_names: Proof.context -> string list
  val consts_named: Proof.context -> string -> string list
  val marks_of: Proof.context -> string -> term list -> (term list * Locale.level * string list) list
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
  val has_K_tag: thm -> bool
  val plain_equal: thm * thm -> bool
  val three_items: thm * thm -> bool
  val diff_K: thm * thm -> bool
  val twin_names: string * string -> term -> term
  val varify_block: term -> term
  val block_lemma: string * string -> int -> thm * thm -> bool
  val phi: string -> thm -> term
  val canonical_vars: term -> term
  val canonical_tvars: term -> term
  val same_shape: term * term -> bool
  val phi_equal: string * string -> thm * thm -> bool
  val proof_after: {apply: bool} -> Proof.context -> thm list -> string -> term -> Proof.state
  val canonical_text: string -> string
  val cases_text: Proof.state -> string list
  val case_names: Proof.state -> string list
  val subgoals: Proof.state -> int
  val assume_in: Proof.context -> (string * typ) list -> string -> string -> thm * Proof.context
  val induct_entry: (Proof.context -> 'a -> thm list) -> Proof.context -> 'a -> thm -> thm option
  val claset_entries: Proof.context -> thm -> (thm * thm * Bires.kind) list
end;

structure Test_Support: TEST_SUPPORT =
struct

val buffer: string list Unsynchronized.ref Thread_Data.var = Thread_Data.var ();

val _ =
  let val original = ! Private_Output.warning_fn in
    Private_Output.warning_fn :=
      (fn ss =>
        ((case Thread_Data.get buffer of
            SOME buf => Unsynchronized.change buf (cons (XML.content_of (YXML.parse_body (implode ss))))
          | NONE => ());
         original ss))
  end;

fun with_warnings f =
  let
    val buf = Unsynchronized.ref [];
    val result = Thread_Data.setmp buffer (SOME buf) f ();
  in (result, rev (! buf)) end;

(*the text after the command word: "name = expression + elements"*)
fun gen_locale_cmd add text thy =
  let
    val toks = filter Token.is_proper (Token.explode (Thy_Header.get_keywords thy) Position.none text);
    val parser =
      Parse.binding --
        Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse_Spec.locale_val) ((([], []), []), []);
    val (name, ((expr, includes), elems)) =
      #1 (Scan.finite Token.stopper (Parse.!!! (parser --| Scan.ahead Parse.eof)) toks);
  in add name Binding.empty includes expr elems thy end;

val light_locale_cmd = gen_locale_cmd Expression.add_light_locale_cmd;
val locale_cmd = gen_locale_cmd Expression.add_locale_cmd;


(*the full names of the theory facts with the given prefix*)
fun facts_under thy prefix =
  Facts.dest_static false [] (Global_Theory.facts_of thy)
  |> map #1 |> filter (String.isPrefix prefix) |> sort_strings;

(*the names of the facts visible in the context, the theory's own included*)
fun visible_fact_names ctxt =
  Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
    (Proof_Context.facts_of ctxt)
  |> map #1 |> sort_strings;

(*the constants of the context (global and local) with the given base name*)
fun consts_named ctxt base =
  #constants (Consts.dest (Proof_Context.consts_of ctxt))
  |> map #1 |> filter (fn c => Long_Name.base_name c = base) |> sort_strings;

(*the recorded marks matching an instance of the locale (plan section 7, preface)*)
fun marks_of ctxt loc insts =
  Locale.matching_marks_of (Context.Proof ctxt) (Locale.check ctxt (loc, Position.none), insts);

(*the binding prefixes of the registrations of the locale, in table order*)
fun registration_prefixes ctxt loc =
  Locale.registrations_of (Context.Proof ctxt) (Locale.check ctxt (loc, Position.none))
  |> map (fn (_, m) => Morphism.binding_prefix m);

(*the right-hand side of an abbreviation, by its full name*)
fun rhs_of ctxt c =
  the (#2 (the (AList.lookup (op =) (#constants (Consts.dest (Proof_Context.consts_of ctxt))) c)));

(*the text after the command word; the obligations are closed by unfold_locales and simp*)
fun interpretation_cmd text thy =
  let
    val toks = filter Token.is_proper (Token.explode (Thy_Header.get_keywords thy) Position.none text);
    val expr =
      #1 (Scan.finite Token.stopper (Parse.!!! (Parse_Spec.locale_expression --| Scan.ahead Parse.eof)) toks);
    fun meth ctxt =
      Method.SIMPLE_METHOD
        (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN ALLGOALS (asm_full_simp_tac ctxt));
  in
    Named_Target.theory_init thy
    |> Interpretation.isar_interpretation_cmd expr
    |> Proof.global_terminal_proof ((Method.Basic meth, Position.no_range), NONE)
    |> Local_Theory.exit_global
  end;

(*"[simp, symmetric]" and the like*)
fun parse_text p thy text =
  let val toks = filter Token.is_proper (Token.explode (Thy_Header.get_keywords thy) Position.none text)
  in #1 (Scan.finite Token.stopper (Parse.!!! (p --| Scan.ahead Parse.eof)) toks) end;

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

(*declare <thms> <attribs>*)
fun declare_in lthy thms atts =
  let val thy = Proof_Context.theory_of lthy in
    Specification.theorems_cmd "" [(Binding.empty_atts,
      [parse_text Parse.thms1 thy thms |> hd |> apsnd (K (attribs_of thy atts))])] [] false lthy
    |> #2
  end;

(*lemmas <name> = <thms> <attribs>, returning the facts the command gives back*)
fun lemmas_in lthy name thms atts =
  let val thy = Proof_Context.theory_of lthy in
    Specification.theorems_cmd "" [((Binding.name name, []),
      [parse_text Parse.thms1 thy thms |> hd |> apsnd (K (attribs_of thy atts))])] [] false lthy
    |>> maps #2
  end;

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

fun assert_twin thy (l, h) =
  let
    fun check what b = if b then () else error ("Twin projection fails: " ^ what);
    val prems_equal = eq_list (op aconv);
    fun thms_equal (thl, thh) =
      prems_equal (map (twin_rename (l, h)) (Thm.prems_of thl), Thm.prems_of thh);

    val pl = Locale.params_of thy l and ph = Locale.params_of thy h;
    val _ = check "params_of"
      (map #1 pl = map #1 ph andalso eq_list Mixfix.equal (map #2 pl, map #2 ph));

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

    fun assumes loc =
      maps (fn Element.Assumes asms => map (fn ((b, _), props) => (Binding.name_of b, map #1 props)) asms
             | _ => []) (Locale.hyp_spec_of thy loc);
    val _ = check "hyp_spec_of"
      (eq_list (fn ((bl, tsl), (bh, tsh)) => bl = bh andalso prems_equal (tsl, tsh))
        (assumes l, assumes h));
  in () end;


(* the comparisons of plan section 7 test 6 (preface: "normal equality" of local copies, the three
   items, "Rule_Cases.get equal up to K", the normalisation phi, the table checks) *)

fun has_K_tag th = AList.defined (op =) (Thm.get_tags th) Exported_Premises.exported_premises_tagN;

(*a local copy whose statement names neither the predicate nor a block constant*)
fun plain_equal (thl, thh) =
  Thm.eq_thm_prop (thl, thh) andalso Rule_Cases.get thl = Rule_Cases.get thh andalso not (has_K_tag thl);

(*any other local copy*)
fun three_items (thl, thh) =
  Exported_Premises.count_of thl = 0 andalso Thm.nprems_of thl = Thm.nprems_of thh andalso
  Rule_Cases.get thl = Rule_Cases.get thh;

fun diff_K (thl, thh) =
  let val (il, nl) = Rule_Cases.get thl and (ih, nh) = Rule_Cases.get thh
  in il = ih andalso nl = nh + Exported_Premises.count_of thl end;

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
fun block_lemma (l, h) premise_count (thl, thh) =
  let
    val k = Exported_Premises.count_of thl;
    val prop = Thm.prop_of thl;
    val stmt = Logic.list_implies (drop k (Logic.strip_imp_prems prop), Logic.strip_imp_concl prop);
  in
    twin_names (l, h) stmt aconv varify_block (Thm.prop_of thh) andalso
    Thm.nprems_of thl = Thm.nprems_of thh + premise_count andalso
    diff_K (thl, thh)
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

(* driving Isar proofs programmatically (test 6, the Rule_Cases rows): the state after
   "lemma goal using facts proof (method)" -- or "apply (method)" -- whose context is read for
   its cases; the facts are given as theorems, the method as text *)

fun proof_after {apply} ctxt facts method goal =
  let
    val (text, _) = Method.read_closure_input ctxt (Input.string method);
    val state = Proof.theorem NONE (K I) [[(goal, [])]] ctxt |> Proof.using [[(facts, [])]];
    val results =
      if apply then Proof.apply (text, Position.no_range) state
      else Proof.proof (SOME (text, Position.no_range)) state;
  in Seq.the_result "proof_after" results end;

(*what print_cases prints, without markup, the schematic variables renamed by order of first
  occurrence: the heavy twin D fixes P, so its rules say ?Pa where the light ones say ?P*)
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
  map (canonical_text o XML.content_of o YXML.parse_body o Pretty.string_of)
    (Proof_Context.pretty_cases (Proof.context_of st));

fun case_names st = map #1 (Proof_Context.dest_cases NONE (Proof.context_of st));

fun subgoals st = Thm.nprems_of (#goal (Proof.goal st));

(*a context with the variables fixed and the assumption name: prop, read there*)
fun assume_in ctxt fixes name prop =
  let
    val (_, ctxt') =
      Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes) ctxt;
    val ([(_, [th])], ctxt'') =
      Proof_Context.add_assms Assumption.assume_export
        [((Binding.name name, []), [(Syntax.read_prop ctxt' prop, [])])] ctxt';
  in (th, ctxt'') end;

(*the Induct table entry Thm.eq_thm_prop with the theorem, if any*)
fun induct_entry find ctxt key th = find_first (fn r => Thm.eq_thm_prop (r, th)) (find ctxt key);

(*the claset entries whose key is Thm.eq_thm_prop with the theorem: key, derived plain rule, kind*)
fun claset_entries ctxt th =
  Classical.dest_decls ctxt (fn (key, _) => Thm.eq_thm_prop (key, th))
  |> map (fn (key, {kind, info = {plain, ...}, ...}) => (key, plain, kind));

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
