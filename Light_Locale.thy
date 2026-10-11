(* Light locale: HOL side (plan section 4).  Plan section 8 step 0 (e): the three keywords and
   command stubs, so that milestone-1 test theories parse.  Until the Pure patch provides
   Expression.add_light_locale_cmd, light_locale behaves as locale; the two structure commands
   are no-ops until milestone 2. *)
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

local

(* Pure.thy:705-713, until the Pure patch exports Parse_Spec.locale_val *)
val locale_context_elements = Scan.repeat1 Parse_Spec.context_element;
val locale_val =
  ((Parse_Spec.locale_expression -- Scan.optional Parse_Spec.opening [])
    || Parse_Spec.opening >> pair ([], []))
  -- Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! locale_context_elements) []
  || locale_context_elements >> pair (([], []), []);

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>light_locale\<close>
    "define light locale (stub: behaves as locale)"
    (Parse.binding --
      Scan.optional (\<^keyword>\<open>=\<close> |-- Parse.!!! locale_val) ((([], []), []), []) -- Parse.opt_begin
      >> (fn ((name, ((expr, includes), elems)), begin) =>
          Toplevel.begin_main_target begin
            (Expression.add_locale_cmd name Binding.empty includes expr elems #> snd)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>set_implicit_structure\<close>
    "set the implicit structure of the current block (stub)"
    (Parse.term >> Light_Locale.set_implicit_structure_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with_implicit_structure\<close>
    "set the implicit structure of the current proof context (stub)"
    (Parse.term >> (fn s =>
      Toplevel.proof (Proof.map_context (Light_Locale.with_implicit_structure_cmd s))));

end
\<close>

end
