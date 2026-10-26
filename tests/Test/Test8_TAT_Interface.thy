(* Plan ai-artifacts/LIGHT_LOCALE_TAT_INTERFACE_PLAN.md section 5, rows A-D: the declaration warning
   and the rebinding warnings as Expression.unfolded_definitions_message returns them, read in the
   context the declaration leaves, equal the warnings the command printed, word for word; the
   rebinding warnings are chosen from the record (Locale.own_params) and come in the parameters'
   order; a name an import passes through cannot be declared again; the text depends on the
   context; Expression.eliminated_params by name and position.  Its own leaf with its own copies of
   Test8_Eliminated's fixtures, because a failing theory-level command ends its theory and a theory
   whose import failed is not run: the mutants of the D20 rows in Test8_Eliminated must not hide
   what these rows do.  The rows are one check_rows list, each declaration made inside its own
   closure, so no row hides another either. *)
theory Test8_TAT_Interface
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale Parent = fixes g :: "'a \<Rightarrow> 'b" and x :: 'a and y :: 'b defines "y \<equiv> g x"
locale Parent0 = fixes g :: "'a \<Rightarrow> 'b" and x :: 'a and y :: 'b
locale Two = fixes g :: "nat \<Rightarrow> nat" and x y z :: nat defines "y \<equiv> g x" and "z \<equiv> g (g x)"
locale X1 = fixes f :: "nat \<Rightarrow> nat" and a b :: nat defines "a \<equiv> f b"
locale X2 = fixes g :: "nat \<Rightarrow> nat" and b c :: nat defines "b \<equiv> g c"
locale Two_r = fixes g :: "nat \<Rightarrow> nat" and x y z :: nat defines "z \<equiv> g (g x)" and "y \<equiv> g x"
locale Infx = fixes plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" and x y :: nat defines "y \<equiv> plus x x"

ML \<open>
val thy = \<^theory>;
(*the warnings in the context the declaration leaves, cleaned as with_warnings cleans*)
fun message_of (name, lthy) =
  map Protocol_Message.clean_output (Expression.unfolded_definitions_message lthy name);
fun message_equals_warnings text =
  let val (decl, ws) = with_warnings (light thy text) in message_of decl = ws end;
(*the parameters a locale defines, by name and position*)
fun eliminated l = map (fn (y, j, _) => (y, j)) (Expression.eliminated_params thy (loc thy l));
\<close>

ML \<open>
val _ = check_rows [
  (*the function's value equals the printed warnings*)
  ("LD1m", fn () => message_equals_warnings "LD1m = Parent f v _ for f v"),
  ("LD2m", fn () => message_equals_warnings "LD2m = X1 + X2"),
  (*the data behind it*)
  ("LD1d", fn () =>
    let val ((name, lthy), _) = with_warnings (light thy "LD1d = Parent f v _ for f v")
    in map (apsnd #1) (Expression.unfolded_definitions lthy name) = [("y", loc thy "Parent")]
    end),
  (*an eliminated name declared again by fixes: no "not bound" line, one rebinding warning*)
  ("LD3", fn () => declares thy "LD3 = X1 + fixes a :: nat" =
    ["The following definitions from `X1` are unfolded.\n  a \<equiv> f b", eliminated_name_warning "a" "X1"]),
  ("LD3m", fn () => message_equals_warnings "LD3m = X1 + fixes a :: nat"),
  (*two names declared again in the for clause: the rebinding warnings in the parameters' order,
    z before y*)
  ("LD4", fn () => declares thy "LD4 = Two g x _ _ for g x z y" =
    ["The following definitions from `Two` are unfolded.\n  y \<equiv> g x\n  z \<equiv> g (g x)",
     eliminated_name_warning "z" "Two", eliminated_name_warning "y" "Two"]),
  ("LD4m", fn () => message_equals_warnings "LD4m = Two g x _ _ for g x z y"),
  (*a name an import passes through cannot be declared again, so own_params is the names the header
    writes (the for half is Test8_Gate's "declared simultaneously" row)*)
  ("LX", fn () =>
    (fails_prefix "Duplicate fixed variable(s)" (light thy "LX = X1 + fixes b :: nat"); true)),
  (*the text depends on the context: a for parameter with infix syntax prints as such in the
    context the declaration leaves, not in the theory's*)
  ("LD5", fn () =>
    let
      val (decl as (name, lthy), ws) = with_warnings (light thy
        "LD5 = Infx f v _ for f :: \"nat \<Rightarrow> nat \<Rightarrow> nat\" (infixl \"\<oplus>\" 65) and v");
      val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);
    in
      message_of decl = ws andalso
      map Protocol_Message.clean_output
        (Expression.unfolded_definitions_message thy_ctxt name) <> ws
    end),
  (*eliminated_params by name and position, sorted by position*)
  ("eliminated_params Parent", fn () => eliminated "Parent" = [("y", 3)]),
  ("eliminated_params Two", fn () => eliminated "Two" = [("y", 3), ("z", 4)]),
  ("eliminated_params Two_r", fn () => eliminated "Two_r" = [("y", 3), ("z", 4)]),
  ("eliminated_params Parent0", fn () => null (eliminated "Parent0"))]
\<close>

end
