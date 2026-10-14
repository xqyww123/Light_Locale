(* Light locale: HOL side (plan section 4).  The light_locale command (item 1), the attributes of
   the predicate facts (item 2), the degeneracy check (item 3) and the check on uses of eliminated
   names (item 4).  The two structure commands are stubs until milestone 2. *)
theory Light_Locale
  imports Main
  keywords
    "light_locale" :: thy_decl_block and
    "set_implicit_structure" :: thy_decl and
    "with_implicit_structure" :: prf_decl
begin

ML \<open>
signature LIGHT_LOCALE =
sig
  val set_implicit_structure_cmd: string -> local_theory -> local_theory
  val with_implicit_structure_cmd: string -> Proof.context -> Proof.context
end;

structure Light_Locale: LIGHT_LOCALE =
struct

fun set_implicit_structure_cmd _ lthy =
  (warning "set_implicit_structure: stub (milestone 2), no effect"; lthy);

fun with_implicit_structure_cmd _ ctxt =
  (warning "with_implicit_structure: stub (milestone 2), no effect"; ctxt);

end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>light_locale\<close> "define light locale"
    (Parse.binding --
      Scan.optional (\<^keyword>\<open>=\<close> |-- Parse.!!! Parse_Spec.locale_val) ((([], []), []), []) --
      Parse.opt_begin
      >> (fn ((name, ((expr, includes), elems)), begin) =>
          Toplevel.begin_main_target begin
            (Expression.add_light_locale_cmd name Binding.empty includes expr elems #> snd)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>set_implicit_structure\<close>
    "set the implicit structure of the current block (stub)"
    (Parse.term >> Light_Locale.set_implicit_structure_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with_implicit_structure\<close>
    "set the implicit structure of the current proof context (stub)"
    (Parse.term >> (fn s =>
      Toplevel.proof (Proof.map_context (Light_Locale.with_implicit_structure_cmd s))));
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
