(* Light locale: HOL side (plan section 4).  The light_locale command (item 1), the attributes of
   the predicate facts (item 2), the degeneracy check (item 3), the check on uses of eliminated
   names (item 4), the structure annotation (item 5) and the two structure commands (items 6, 7). *)
theory Light_Locale
  imports Main
  keywords
    "light_locale" :: thy_decl_block and
    "implicit_structure" :: quasi_command and
    "no_implicit_structure" :: quasi_command and
    "set_implicit_structure" :: thy_decl and
    "with_implicit_structure" :: prf_decl
begin

subsection \<open>The commands (plan section 4 items 1, 6 and 7)\<close>

ML \<open>
signature LIGHT_LOCALE =
sig
  val light_locale_header: (binding * ((Expression.expression * Bundle.xname list) *
    (string Syntax_Trans.implicit_structure_spec * Element.context list))) parser
  val set_implicit_structure_cmd: string -> local_theory -> local_theory
  val with_implicit_structure_cmd: string -> Proof.context -> Proof.context
end;

structure Light_Locale: LIGHT_LOCALE =
struct

(* The type variable guard's message (plan section 4 item 6): for every undeclared type variable,
   in order of occurrence, the best carrier whose type mentions it -- a bound variable the body
   uses or a free variable, then a number, then a constant, then any other bound variable; not at
   a function head before at one, leftmost first -- each carrier listed once, in that order. *)

datatype carrier = Variable of string | Number of int | Printed of term;

(*the bound variables of the value renamed before the printer sees it: the names the printer
  avoids (its own avoidance set, plus the default structure) are declared first, then the
  binder names are made pairwise distinct against them, so the printer renames none of them and
  the carriers name what the printed value shows*)
fun rename_bounds ctxt v =
  let
    fun collect (Abs (x, _, b)) = not (Name.is_internal x) ? cons x #> collect b
      | collect (t $ u) = collect t #> collect u
      | collect _ = I;
    val names =
      Name.variant_names_build
        (Syntax_Trans.declare_term_names ctxt v #>
          fold Name.declare (the_list (Syntax_Trans.default_struct ctxt)))
        (map (rpair ()) (rev (collect v [])))
      |> map #1;
    fun rename (Abs (x, T, b)) names =
          if Name.is_internal x then apfst (fn b' => Abs (x, T, b')) (rename b names)
          else
            (case names of
              x' :: names' => apfst (fn b' => Abs (x', T, b')) (rename b names')
            | [] => raise Fail "rename_bounds")
      | rename (t $ u) names =
          let
            val (t', names') = rename t names;
            val (u', names'') = rename u names';
          in (t' $ u', names'') end
      | rename t names = (t, names);
  in #1 (rename v names) end;

(*the candidates in traversal order: category, at a function head, carrier, type; a number is one
  candidate, its constants none*)
fun candidates v =
  let
    fun atoms head t =
      (case try HOLogic.dest_number t of
        SOME (T, n) => cons (2, head, Number n, T)
      | NONE =>
          (case t of
            Abs (x, T, b) =>
              cons (if not (Name.is_internal x) andalso Term.is_dependent b then 1 else 4, false,
                  Variable (if Name.is_internal x then "_" else x), T)
              #> atoms false b
          | _ $ _ =>
              let val (h, args) = Term.strip_comb t
              in atoms true h #> fold (atoms false) args end
          | Const (_, T) => cons (3, head, Printed t, T)
          | Free (_, T) => cons (1, head, Printed t, T)
          | _ => I));
  in rev (atoms false v []) end;

fun undeclared_message ctxt0 t undeclared =
  let
    val ctxt = Config.put Syntax_Trans.eta_contract false ctxt0;
    val thy = Proof_Context.theory_of ctxt;
    val v = rename_bounds ctxt t;
    fun mentions x (_, _, _, T) = exists (fn (y, _) => y = x) (Term.add_tfreesT T []);
    val key = fn ((category, head, _, _), i) => (category, (head, i));
    fun best x =
      map_index swap (candidates v)
      |> filter (mentions x o #1)
      |> sort (prod_ord int_ord (prod_ord bool_ord int_ord) o apply2 key)
      |> try hd;
    val chosen =
      fold (fn x => fn acc =>
        (case best x of
          SOME (cand, i) => if member (op =) (map #2 acc) i then acc else acc @ [(cand, i)]
        | NONE => acc)) undeclared [];
    (*sorts are printed only when an undeclared variable of the type has a non-trivial one*)
    fun carrier ((_, _, c, T), _) =
      let
        val nontrivial =
          exists (fn (x, S) =>
              member (op =) undeclared x andalso not (Sign.subsort thy (Sign.defaultS thy, S)))
            (Term.add_tfreesT T []);
        val text =
          (case c of
            Variable x => x
          | Number n => if n < 0 then "- " ^ string_of_int (~ n) else string_of_int n
          | Printed u => Syntax.string_of_term ctxt u);
      in "`" ^ text ^ " :: " ^ Syntax.string_of_typ (Config.put show_sorts nontrivial ctxt) T ^ "`" end;
    val carriers = map carrier chosen;
    fun listed [c] = c
      | listed cs = commas (take (length cs - 1) cs) ^ " and " ^ List.last cs;
  in
    "Undeclared type variable" ^ (if length undeclared = 1 then " " else "s ") ^ commas undeclared ^
    " in the implicit structure `" ^ Syntax.string_of_term ctxt v ^ "`, where " ^ listed carriers ^
    (if length carriers = 1 then " requires a concrete type annotation."
     else " require concrete type annotations.")
  end;

(*the two guards (plan section 4 item 6; header plan section 3.4) with explicit inputs: the
  variables allowed, each with the name the second sentence prints; that sentence, built from the
  printed names, or the one for no variables; and the test on type variables*)
fun guard ctxt {allowed, tfree_ok, listed, none} t =
  let
    val undeclared = filter_out (member (op =) (map #1 allowed)) (rev (Term.add_free_names t []));
    val second = if null allowed then none else listed (distinct (op =) (map #2 allowed));
  in
    (case undeclared of
      [] => ()
    | [x] =>
        error ("Illegal undeclared variable " ^ quote x ^ " in the implicit structure. " ^ second)
    | xs =>
        error ("Illegal undeclared variables " ^ commas_quote xs ^
          " in the implicit structure. " ^ second));
    (case filter_out tfree_ok (rev (Term.add_tfree_names t [])) of
      [] => ()
    | tfrees => error (undeclared_message ctxt t tfrees))
  end;

(*the header: the parameters being declared*)
fun header_guard params =
  let val tfrees = fold (Term.add_tfree_namesT o #2) params [] in
   {allowed = map (fn (x, _) => (x, x)) params,
    tfree_ok = member (op =) tfrees,
    listed = fn xs => "Only the parameters being declared may occur here: " ^ commas_quote xs ^ ".",
    none = "No parameters are being declared in the locale, so no variable may occur here."}
  end;

(*a block or a proof: the variables fixed in the context, in order of declaration --
  allowed by the names a read term carries (a proof's skolem names), listed by their external
  names; the placeholder, whose external name is internal, is not a variable*)
fun fixed_guard ctxt =
 {allowed = map swap (filter_out (Name.is_internal o #1) (Variable.dest_fixes ctxt)),
  tfree_ok = Variable.is_declared ctxt,
  listed = fn xs => "Only variables fixed in this context may occur here: " ^ commas_quote xs ^ ".",
  none = "No variables are fixed in this context, so no variable may occur here."};

(*the empty text, blanks included, cancels (header plan section 2 item 9); a value is read and
  passed through fixed_guard here, so that every command reading one guards it; the source explode
  drops the padding of a token's text*)
fun cancel_or_declare ctxt s =
  if forall (Symbol.is_blank o Symbol_Pos.symbol) (Input.source_explode (Syntax.read_input s))
  then Syntax_Trans.Cancel
  else
    let val t = Syntax.read_term ctxt s
    in guard ctxt (fixed_guard ctxt) t; Syntax_Trans.Declare t end;

fun install (Syntax_Trans.Declare t) = Proof_Context.declare_implicit_structure t
  | install spec = Syntax_Trans.put_implicit_structure spec;

(*plan decision 16 (d): block scope -- the innermost snapshot and the live context.  A locale's
  implicit structure is declared in its header only (header plan section 2 item 1): no block
  whose bottom target is a locale may set one*)
fun set_implicit_structure_cmd s lthy =
  if Named_Target.is_theory lthy then
    error "You cannot set the implicit structure at the theory level. \
      \Use it inside a context block."
  else if is_some (Named_Target.bottom_locale_of lthy) then
    error "You cannot set the implicit structure inside a locale. \
      \Declare it in the header of a light locale with implicit_structure instead."
  else
    let val spec = cancel_or_declare lthy s in
      Local_Theory.map_contexts (fn level => level >= Local_Theory.level lthy - 1 ? install spec)
        lthy
    end;

fun with_implicit_structure_cmd s ctxt = install (cancel_or_declare ctxt s) ctxt;

(*the header text after the command word (header plan section 3.2): the elements may hold at
  most one implicit_structure t / no_implicit_structure, anywhere among them*)
val light_locale_header =
  Parse.binding --
    Scan.optional (\<^keyword>\<open>=\<close> |--
      Parse.!!! (Parse_Spec.locale_val'
        [(\<^keyword>\<open>implicit_structure\<close>, Parse.term >> Syntax_Trans.Declare),
         (\<^keyword>\<open>no_implicit_structure\<close>, Scan.succeed Syntax_Trans.Cancel)]))
      ((([], []), []), ([], []))
  >> (fn (name, ((expr, includes), (elems, extras))) =>
      (name, ((expr, includes),
        ((case extras of
          [] => Syntax_Trans.Inherit
        | [spec] => spec
        | _ => error "A light locale header declares at most one implicit structure"), elems))));

(*the two checks of a light header run inside Pure through these hooks (header plan section
  3.4), so that every way of declaring a light locale meets them*)
val _ =
  Theory.setup
   (Locale.set_light_own_structure_check (fn _ => fn names =>
      error ("A light locale does not declare (structure) parameters: " ^ commas_quote names ^
        (case names of
          [x] => ". Write implicit_structure " ^ x ^ " instead."
        | _ => ". Write implicit_structure with one of them instead."))) #>
    Locale.set_light_structure_guard (fn ctxt => fn {params, declared} =>
      guard ctxt (header_guard params) declared));

end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>light_locale\<close> "define light locale"
    (Light_Locale.light_locale_header -- Parse.opt_begin
      >> (fn ((name, ((expr, includes), (spec, elems))), begin) =>
          Toplevel.begin_main_target begin
            (Expression.add_light_locale_cmd name Binding.empty includes expr spec elems #> snd)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>set_implicit_structure\<close>
    "set the implicit structure of the current block"
    (Parse.term >> Light_Locale.set_implicit_structure_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with_implicit_structure\<close>
    "set the implicit structure of the current proof context"
    (Parse.term >> (fn s =>
      Toplevel.proof (Proof.map_context (Light_Locale.with_implicit_structure_cmd s))));
\<close>


subsection \<open>Structure annotation (plan decision 17, section 4 item 5)\<close>

syntax
  "_implicit_structure" :: "logic \<Rightarrow> logic \<Rightarrow> logic"
    (\<open>_ \<lbrakk>structure: _\<rbrakk>\<close> [0, 10] 0)
  "_implicit_structure'" :: "logic \<Rightarrow> prop \<Rightarrow> prop"
    (\<open>(2\<lbrakk>structure: _\<rbrakk>/./  _)\<close> [10, 0] 0)
  (*the candidate node takes the body (wrap below); the types here only place the node at the
    body's nonterminal*)
  "_implicit_structure_candidate" :: "logic \<Rightarrow> logic"
  "_implicit_structure_candidate'" :: "prop \<Rightarrow> prop"

ML \<open>
val show_implicit_structure =
  Attrib.setup_config_bool \<^binding>\<open>show_implicit_structure\<close> (K false);

local

val empty_subscript =
  Ast.Appl [Ast.Constant \<^syntax_const>\<open>_struct\<close>, Ast.Constant \<^syntax_const>\<open>_indexdefault\<close>];

(* Reading: the annotation means S written at every empty subscript of the body.  The empty
   subscripts become S before the parse rules and the term-level translations run, so a binder of
   the body binds the names of S as it would had S been written there.  S itself is not traversed,
   nor are the copies put in. *)

fun fill s (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_index\<close>, x]) =
      Ast.Appl [Ast.Constant \<^syntax_const>\<open>_index\<close>, if x = empty_subscript then s else fill s x]
  | fill s (Ast.Appl asts) = Ast.Appl (map (fill s) asts)
  | fill _ ast = ast;

(* Printing (plan decision 17): at the last uncheck stage the whole term is wrapped in a candidate
   node, whose print ast translation decides on the ast the print rules have produced -- the
   outermost index occurrences of the body all the same S, S not the default structure, S closed
   -- and then elides every one of them and puts S into the annotation. *)

val candidate = \<^syntax_const>\<open>_implicit_structure_candidate\<close>;
val candidate' = \<^syntax_const>\<open>_implicit_structure_candidate'\<close>;

fun is_candidate t =
  (case Term.head_of t of Const (c, _) => c = candidate orelse c = candidate' | _ => false);

(*the candidate node around the whole term, at the last uncheck stage, so that no other uncheck
  function sees it; a term already wrapped stays, since the stage iterates to a fixed point*)
fun wrap ctxt t =
  if not (Config.get ctxt show_implicit_structure) orelse Config.get ctxt show_structs orelse
    is_candidate t
  then t
  else Syntax.const (if (fastype_of t = propT handle TERM _ => false) then candidate' else candidate) $ t;

(*the outermost index occurrences of an ast, in ast order, and the ast with each of them
  replaced by the empty subscript; fill s undoes it*)
fun elide (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_index\<close>, x]) =
      (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_index\<close>, empty_subscript], [x])
  | elide (Ast.Appl asts) = split_list (map elide asts) |>> Ast.Appl ||> flat
  | elide ast = (ast, []);

(*the ast without its type constraints, at every depth, except those on binders while types are
  printed: compared is what is printed, and the constraints differ between the copies of S --
  show_types types a variable at its first occurrence only, show_markup puts one on every atom
  -- but a binder's type is printed in every copy, and copies differing there are different
  structures (the annotation would read back with one binder type for all)*)
fun unconstrain ctxt =
  let
    val binder_types = Config.get ctxt show_types orelse Config.get ctxt show_sorts;
    fun strip (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_constrain\<close>, ast, ty]) =
          (case ast of
            Ast.Appl [Ast.Constant \<^syntax_const>\<open>_bound\<close>, _] =>
              if binder_types then Ast.Appl [Ast.Constant \<^syntax_const>\<open>_constrain\<close>, ast, ty] else ast
          | _ => strip ast)
      | strip (Ast.Appl asts) = Ast.Appl (map strip asts)
      | strip ast = ast;
  in strip end;

(*the copy of S to print is the one with the most type constraints: the copy that prune_types
  reached first carries every constraint the other copies do and the variable types besides*)
fun constraints (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_constrain\<close>, ast, _]) = 1 + constraints ast
  | constraints (Ast.Appl asts) = fold (Integer.add o constraints) asts 0
  | constraints _ = 0;

val most_constrained = foldl1 (fn (a, b) => if constraints b > constraints a then b else a);

(*the default structure: the empty subscript -- the first layer's head while the implicit
  structure is inherited (Syntax_Trans.inherited_struct), or the second layer's value, which
  Pure's elision has replaced wherever it stands at an index position (also one a translation
  defines, also when it holds an abbreviation, also the placeholder; plan section 11 (39))*)
fun is_default s = s = empty_subscript;

fun has_loose (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_loose\<close>, _]) = true
  | has_loose (Ast.Appl asts) = exists has_loose asts
  | has_loose _ = false;

fun bound_names (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_bound\<close>, Ast.Variable y]) = cons y
  | bound_names (Ast.Appl asts) = fold bound_names asts
  | bound_names _ = I;

(*the name check (plan decision 17): S is closed -- no loose bound variable, and no bound
  variable of S whose binder is a binder of the body, which shows as a _bound of the elided body
  of the same name; S's own binders pass, except one named like a binder of the body, which the
  check refuses on the safe side*)
fun closed body' s =
  not (has_loose s) andalso null (inter (op =) (bound_names body' []) (bound_names s []));

fun candidate_ast_tr' annotation ctxt [body] =
      let val (body', occurrences) = elide body in
        (case distinct (op =) (map (unconstrain ctxt) occurrences) of
          [s] =>
            if is_default s orelse not (closed body' s) then body
            else annotation (most_constrained occurrences, body')
        | _ => body)
      end
  | candidate_ast_tr' _ _ asts = raise Ast.AST ("candidate_ast_tr'", asts);

in

val _ =
  Theory.setup
   (Sign.parse_ast_translation
     [(\<^syntax_const>\<open>_implicit_structure\<close>,
        fn _ => fn [body, s] => fill s body | asts => raise Ast.AST ("_implicit_structure", asts)),
      (\<^syntax_const>\<open>_implicit_structure'\<close>,
        fn _ => fn [s, body] => fill s body | asts => raise Ast.AST ("_implicit_structure'", asts))] #>
    Context.theory_map
     (Syntax_Phases.term_uncheck 100 "light_locale_implicit_structure"
       (fn ctxt => map (wrap ctxt))) #>
    Sign.print_ast_translation
     [(candidate,
        candidate_ast_tr' (fn (s, body') =>
          Ast.Appl [Ast.Constant \<^syntax_const>\<open>_implicit_structure\<close>, body', s])),
      (candidate',
        candidate_ast_tr' (fn (s, body') =>
          Ast.Appl [Ast.Constant \<^syntax_const>\<open>_implicit_structure'\<close>, s, body']))]);

end;
\<close>


subsection \<open>The attributes of the predicate facts (plan decision 11)\<close>

setup \<open>Locale.set_light_axioms_attributes @{attributes [simp, intro!]}\<close>


subsection \<open>Degeneracy check (plan decision 12)\<close>

ML \<open>
local

(*the left-hand sides of the rules the simpset's own mksimps makes, except a variable: the
  simpset stores that rule in its eq_True form, led by a constant (raw_simplifier.ML mk_rrule)*)
fun simp_lhss thy_ctxt th =
  Simplifier.mksimps thy_ctxt (Thm.transfer' thy_ctxt th)
  |> map (#1 o Logic.dest_equals o Thm.concl_of)
  |> filter_out (is_Var o Envir.eta_contract);

fun major_prem kind _ th = the_list (try (Thm.major_prem_of o Bires.kind_make_elim kind) th);

(*per checked attribute, by full name: the terms its registry indexes, which part of the rule they
  are, and the tool that uses them.  The Context_Rules declarations Pure.intro/elim/dest are not
  checked: packages put them on internal rules (the graph rules of fun, inductive.ML:1059)*)
val kinds =
  let
    fun name a = Attrib.check_name \<^context> (a, Position.none);
    val simp = (simp_lhss, "left-hand side", "simplifier");
  in
    [(name "simp", simp), (name "iff", simp),
     (name "intro", (K (single o Thm.concl_of), "conclusion", "classical reasoner")),
     (name "elim", (major_prem Bires.elim_kind, "major premise", "classical reasoner")),
     (name "dest", (major_prem Bires.dest_kind, "major premise", "classical reasoner"))]
  end;

(*the name of a schematic variable at the head, or of one applied as a non-pattern*)
fun degeneracy thy_ctxt t0 =
  let
    val t = Envir.beta_eta_contract (Object_Logic.drop_judgment thy_ctxt t0);
    fun non_pattern (Abs (_, _, b)) = non_pattern b
      | non_pattern u =
          (case Term.strip_comb u of
            (Var ((x, _), _), _) => if Pattern.pattern u then NONE else SOME x
          | (_, args) => get_first non_pattern args);
  in
    (case Term.head_of t of
      Var ((x, _), _) => SOME (true, x)
    | _ => Option.map (pair false) (non_pattern t))
  end;

fun degeneracy_warning params name kind site tool (led, x) =
  let
    val how =
      (case (member (op =) params x, led) of
        (true, true) => "is led by locale parameter `" ^ x ^ "` which will be a schematic variable"
      | (true, false) =>
          "contains locale parameter `" ^ x ^
            "` applied to arguments, which will be a higher-order pattern"
      | (false, true) => "is led by the schematic variable `?" ^ x ^ "`"
      | (false, false) =>
          "contains the schematic variable `?" ^ x ^
            "` applied to arguments, which will be a higher-order pattern");
  in
    "Light locale rule " ^ (if name = "" then "" else "`" ^ name ^ "` ") ^ "[" ^ kind ^ "]: its " ^
      site ^ " " ^ how ^ " in the system registry. The system " ^ tool ^
      " may not work as you expect. Consider stating it on a derived constant."
  end;

fun check_src thy_ctxt params name th src =
  let
    val attr = #1 (Token.name_of_src src);
    val del = exists (fn tok => Token.content_of tok = "del") (Token.args_of_src src);
  in
    (case AList.lookup (op =) kinds attr of
      SOME (indexed, site, tool) =>
        if del then ()
        else
          (case get_first (degeneracy thy_ctxt) (indexed thy_ctxt th) of
            SOME hit =>
              warning (degeneracy_warning params name (Long_Name.base_name attr) site tool hit)
          | NONE => ())
    | NONE => ())
  end;

in

fun degeneracy_check locale facts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    (*where the theory registries run; in lthy the parameter names are fixed and HOL's mksimps
      renames the parameter variables, which the message would then not call parameters*)
    val thy_ctxt = Proof_Context.init_global thy;
    val params = map (#1 o #1) (Locale.params_of thy locale);
  in
    facts |> List.app (fn ((b, _), fact) =>
      let val name = if Binding.is_empty b then "" else Local_Theory.full_name lthy b in
        fact |> List.app (fn (ths, srcs) =>
          ths |> List.app (fn th => List.app (check_src thy_ctxt params name th) srcs))
      end)
  end;

end;

val _ = Theory.setup (Locale.set_light_degeneracy_check degeneracy_check);
\<close>


subsection \<open>Uses of eliminated names (plan decision 1)\<close>

ML \<open>
(*an unfixed free variable with the name and a compatible type of an eliminated parameter*)
fun eliminated_names_check ts ctxt =
  let
    val table = Locale.eliminated_names_of ctxt;
    fun hit (Free (x, T)) =
          (case Symtab.lookup table x of
            SOME (loc, v) =>
              (not (Variable.is_fixed ctxt x) andalso Type.could_unify (T, Term.fastype_of v))
                ? insert (eq_fst (op =)) (x, loc)
          | NONE => I)
      | hit _ = I;
    val hits =
      if Symtab.is_empty table orelse not (Context_Position.is_visible ctxt) then []
      else rev (fold (Term.fold_aterms hit) ts []);
    val _ = List.app (Locale.eliminated_name_warning ctxt) hits;
  in NONE end;

val _ =
  Theory.setup (Context.theory_map
    (Syntax_Phases.term_check' 50 "light_locale_eliminated_names" eliminated_names_check));
\<close>

end
