(* Plan section 7 test 9 (structure): the structure annotation (plan decision 17, section 4
   item 5; rows at plan 5268-5279).  Reading: the nine statement shapes, nesting, the mixed
   forms, the two spellings of the closing bracket, an unrelated set-bracket notation, capture --
   S is written at every empty subscript, so a binder of the body binds the names of S -- and an
   empty subscript inside S.  Printing with show_implicit_structure: the decision on the printed
   ast -- the outermost index occurrences of every kind of index syntax (a constant's own mixfix,
   a translation, also one whose index variable is nested, a fixed variable) all the same S, S not
   the default structure (the empty subscript: Pure has elided the second layer's value and the
   placeholder at every index position), S closed -- dispatch by type, three print
   modes round trip, the forced line break, the two print differences of the annotation
   (show_types, binder names), a notation that hides a binder, what the uncheck stages expose.
   The helpers and the rows wrapped in both_modes run in batch and as PIDE prints (show_markup
   on), each mode held to the same expected text; the other rows run in batch only.  The
   rows the mutation checks of the AST plan (section 5) name each sit in an ML command of their
   own; the first failing row ends the leaf.  An interpret leaves the two layers alone. *)
theory Test9_Annotation
  imports Test9_Fixtures
begin

consts sem :: "'a \<Rightarrow> 'a set"
syntax "_sem" :: "'a \<Rightarrow> 'a set"  (\<open>\<lbrakk>_\<rbrakk>\<close>)
translations "\<lbrakk>M\<rbrakk>" == "CONST sem M"

(* an index syntax whose index variable is nested in the term side of its translation *)
consts
  bar :: "'a monoid \<Rightarrow> 'a \<Rightarrow> 'a"
  baz :: "'a monoid \<Rightarrow> 'a monoid"
syntax "_bar" :: "index \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>BAR_ _\<close> [1000, 1000] 999)
translations "BAR\<^bsub>G\<^esub> x" \<rightleftharpoons> "CONST bar (CONST baz G) x"

(* the same with a function-valued middle node, so that the term can hold an abstraction there *)
consts
  bar2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  baz2 :: "'a monoid \<Rightarrow> 'a \<Rightarrow> 'a"
syntax "_bar2" :: "index \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>BAR2_ _\<close> [1000, 1000] 999)
translations "BAR2\<^bsub>G\<^esub> x" \<rightleftharpoons> "CONST bar2 (CONST baz2 G) x"

(* a quote/antiquote notation (HOL/ex/Antiquote.thy): assn (\<lambda>s. b) prints as \<lbrace>b\<rbrace>, an
   application f s inside as \<acute>f -- the printer hides the binder s *)
consts assn :: "('s \<Rightarrow> bool) \<Rightarrow> 's set"
syntax
  "_assn" :: "'a \<Rightarrow> 'a"  (\<open>\<lbrace>_\<rbrace>\<close> [0] 1000)
  "_antiquote" :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a"  (\<open>\<acute>_\<close> [1000] 1000)
syntax_consts "_assn" \<rightleftharpoons> assn
parse_translation \<open>
  [Syntax_Trans.quote_antiquote_tr \<^syntax_const>\<open>_assn\<close> \<^syntax_const>\<open>_antiquote\<close>
    \<^const_syntax>\<open>assn\<close>]
\<close>
print_translation \<open>
  [Syntax_Trans.quote_antiquote_tr' \<^syntax_const>\<open>_assn\<close> \<^syntax_const>\<open>_antiquote\<close>
    \<^const_syntax>\<open>assn\<close>]
\<close>

ML \<open>
open Test_Support;

val on = Config.put show_implicit_structure true;

(*a printing check runs in batch and as PIDE prints -- show_markup on, the only print setting
  that differs between the two (isabelle_process.ML) -- each mode held to the same expectation*)
fun both_modes check ctxt = (check ctxt; check (Config.put show_markup true ctxt));

(*printed as the expected text, which reads back as the input (round_trips of Test_Support)*)
fun annotated ctxt text expected =
  both_modes (fn ctxt => (prints_as ctxt text expected; \<^assert> (round_trips ctxt (reads ctxt text)))) ctxt;

(*printed without an annotation, and the output reads back as the input*)
fun left_alone ctxt text =
  both_modes (fn ctxt =>
    let val t = reads ctxt text in
      if not (String.isSubstring "structure:" (shows ctxt t)) andalso round_trips ctxt t then ()
      else error ("not left alone or no round trip: " ^ text ^ " -> " ^ shows ctxt t)
    end) ctxt;

(*printed as the expected text, which reads back as the input up to eta (the printer contracts)*)
fun annotated_eta ctxt text expected =
  both_modes (fn ctxt =>
    let val t = reads ctxt text in
      prints_as ctxt text expected; \<^assert> (Envir.aeconv (reads ctxt (shows ctxt t), t))
    end) ctxt;

(*readable, one parse tree: no ambiguity warning*)
fun unambiguous read ctxt text =
  let val (_, ws) = with_warnings (fn () => read ctxt text)
  in \<^assert> (not (exists (String.isSubstring "Ambiguous") ws)) end;

(*printed in a print mode, read back without it*)
fun round_trip_in_mode ctxt read mode t =
  read ctxt (clean (Print_Mode.setmp [mode] (Syntax.string_of_term ctxt) t)) aconv t;

(*the prefix form: the annotation, the dot, white space, the body*)
fun prefix_form s annotation body =
  let val (before_dot, rest) = chop_prefix (fn c => c <> ".") (Symbol.explode s) in
    \<^assert> (implode before_dot = annotation andalso
      implode (drop_prefix (fn c => c = " " orelse c = "\n") (tl rest)) = body)
  end;

(*the index arguments of the multiplication, in order*)
fun mult_args (t $ u) =
      (case t of Const (\<^const_name>\<open>mult\<close>, _) => [u] | _ => []) @ mult_args t @ mult_args u
  | mult_args (Abs (_, _, b)) = mult_args b
  | mult_args _ = [];

(*capture (plan 5273): S is written at every empty subscript, so the binder of the body binds
  the p of S -- the annotation after the quantification (the postfix form, priority 0, takes the
  whole quantification as its body) and inside it; both read as the term the explicit subscripts
  give*)
fun captured ctxt =
  let
    val explicit = Syntax.read_prop ctxt "\<forall>p. x \<otimes>\<^bsub>tmk p\<^esub> y = y \<otimes>\<^bsub>tmk p\<^esub> x";
    val _ = \<^assert> (not (null (mult_args explicit)) andalso forall Term.is_open (mult_args explicit));
    val outer = Syntax.read_prop ctxt "\<forall>p. x \<otimes> y = y \<otimes> x \<lbrakk>structure: tmk p\<rbrakk>";
    val inner = Syntax.read_prop ctxt "\<forall>p. (x \<otimes> y = y \<otimes> x \<lbrakk>structure: tmk p\<rbrakk>)";
  in \<^assert> (outer aconv explicit andalso inner aconv explicit) end;

(*the candidate node the uncheck stage puts around a term (Light_Locale, printing side), and
  whether the uncheck stages leave one on a term*)
fun is_candidate t =
  (case Term.head_of t of
    Const (c, _) =>
      c = \<^syntax_const>\<open>_implicit_structure_candidate\<close> orelse
      c = \<^syntax_const>\<open>_implicit_structure_candidate'\<close>
  | _ => false);
fun unchecks_to_candidate ctxt t = is_candidate (singleton (Syntax.uncheck_terms ctxt) t);
\<close>


subsection \<open>Reading (plan 5272-5274)\<close>

(* the assertion rows are ML commands: the first failing row ends the leaf and is reported, the
   rows after it are not run *)
ML \<open>local
val ctxt = \<^context>;
val whole = "\<lbrakk>structure: tmk q\<rbrakk>. x \<otimes> y = y \<otimes> x";
val nested_prefix = "\<lbrakk>structure: tmk q\<rbrakk>. \<lbrakk>structure: tmk r\<rbrakk>. x \<otimes> y = z";
val nested_inside = "\<lbrakk>structure: tmk q\<rbrakk>. P (x \<otimes> y \<lbrakk>structure: tmk r\<rbrakk>) \<otimes> z = w";
val set_bracket = "\<forall>u \<in> \<lbrakk>M\<rbrakk>. u > (0 :: nat)";
val shapes =
 [whole,
  "\<lbrakk>structure: tmk q\<rbrakk>. x \<otimes> y = z \<Longrightarrow> u \<otimes> v = w",
  "\<lbrakk>structure: tmk q\<rbrakk>. x = z \<Longrightarrow> u \<otimes> v = w",
  "\<lbrakk>structure: tmk q\<rbrakk>. (x \<otimes> y = z \<Longrightarrow> u \<otimes> v = w)",
  "\<lbrakk>structure: tmk q\<rbrakk>. \<And>r. x \<otimes> y = r",
  "\<lbrakk>structure: tmk q\<rbrakk>. (x \<otimes> y = z) &&& (u \<otimes> v = w)",
  "\<lbrakk>structure: tmk q\<rbrakk>. x \<otimes> y = z \<longrightarrow> u \<otimes> v = w",
  "\<lbrakk>structure: tmk q\<rbrakk>. \<lbrakk>x \<otimes> y = z; True\<rbrakk> \<Longrightarrow> u \<otimes> v = w",
  nested_prefix,
  nested_inside,
  "\<lbrakk>structure: tmk q\<rbrakk> . x \<otimes> y = y \<otimes> x",
  "\<lbrakk>PROP P; PROP Q\<rbrakk> \<Longrightarrow> PROP R",
  "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q",
  set_bracket];
val _ = List.app (unambiguous Syntax.read_prop ctxt) shapes;
val _ = List.app (unambiguous Syntax.read_term ctxt)
 ["x \<otimes> y = y \<otimes> x \<lbrakk>structure: tmk q\<rbrakk>",
  "(x \<otimes> (y \<oplus> z \<lbrakk>structure: tmk r\<rbrakk>)) \<lbrakk>structure: tmk q\<rbrakk>",
  "u \<otimes> v \<lbrakk>structure: if b then tmk q else tmk r\<rbrakk>"];
(*the annotation denotes the structure: whole statement and nesting, inner wins*)
val _ = \<^assert> (Syntax.read_prop ctxt whole aconv
  Syntax.read_prop ctxt "x \<otimes>\<^bsub>tmk q\<^esub> y = y \<otimes>\<^bsub>tmk q\<^esub> x");
val _ = \<^assert> (Syntax.read_prop ctxt nested_prefix aconv
  Syntax.read_prop ctxt "x \<otimes>\<^bsub>tmk r\<^esub> y = z");
val _ = \<^assert> (Syntax.read_prop ctxt nested_inside aconv
  Syntax.read_prop ctxt "P (x \<otimes>\<^bsub>tmk r\<^esub> y) \<otimes>\<^bsub>tmk q\<^esub> z = w");
val _ = \<^assert> (Syntax.read_prop ctxt set_bracket aconv
  Syntax.read_prop ctxt "\<forall>u \<in> sem M. u > (0 :: nat)");
in end\<close>

(* capture (captured above): with p not fixed and with p fixed *)
ML \<open>val _ = captured \<^context>\<close>
context
  fixes p :: 'q
begin
ML \<open>val _ = captured \<^context>\<close>
end
(* the prefix form before the quantification; a quantification over one of two conjuncts: the p
   under the binder is bound, the other p is free *)
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (Syntax.read_prop ctxt "\<lbrakk>structure: tmk p\<rbrakk>. \<forall>p. x \<otimes> y = z" aconv
  Syntax.read_prop ctxt "\<forall>p. x \<otimes>\<^bsub>tmk p\<^esub> y = z");
val _ = \<^assert> (Syntax.read_prop ctxt "(\<forall>p. x \<otimes> y = y) \<and> u \<otimes> v = v \<lbrakk>structure: tmk p\<rbrakk>" aconv
  Syntax.read_prop ctxt "(\<forall>p. x \<otimes>\<^bsub>tmk p\<^esub> y = y) \<and> u \<otimes>\<^bsub>tmk p\<^esub> v = v");
in end\<close>

(* an empty subscript inside S: S is filled into the body only, so the inner annotation leaves
   it, and the outer annotation fills it in turn; in group_hom it denotes the first layer's G *)
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (reads ctxt "(x \<otimes> y \<lbrakk>structure: tmk (a \<otimes> b)\<rbrakk>) \<lbrakk>structure: tmk r\<rbrakk>" aconv
  reads ctxt "x \<otimes>\<^bsub>tmk (a \<otimes>\<^bsub>tmk r\<^esub> b)\<^esub> y");
in end\<close>
context group_hom
begin
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (reads ctxt "x \<otimes> y \<lbrakk>structure: tmk (a \<otimes> b)\<rbrakk>" aconv
  reads ctxt "x \<otimes>\<^bsub>tmk (a \<otimes>\<^bsub>G\<^esub> b)\<^esub> y");
in end\<close>
end


subsection \<open>Printing (plan 5268-5271)\<close>

context group_hom
begin
ML \<open>val _ = \<^assert> (layers (on \<^context>) = (SOME "G", NONE))\<close>
(* every index occurrence H, another structure than the default: annotated, postfix for a term,
   prefix for a proposition; idempotent *)
ML \<open>val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y" "x \<otimes> y \<lbrakk>structure: H\<rbrakk>"\<close>
ML \<open>local
val ctxt = on \<^context>;
val p = Syntax.read_prop ctxt "x \<otimes>\<^bsub>H\<^esub> y = y \<otimes>\<^bsub>H\<^esub> x";
val _ = prefix_form (shows ctxt p) "\<lbrakk>structure: H\<rbrakk>" "x \<otimes> y = y \<otimes> x";
val _ = \<^assert> (shows ctxt p = shows ctxt (Syntax.read_prop ctxt (shows ctxt p)));
in end\<close>
(* the default structure stays bare: the empty subscript the first layer leaves is the default *)
ML \<open>val _ = both_modes (fn ctxt => prints_as ctxt "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes> y") (on \<^context>)\<close>
(* two structures: explicit subscripts, no annotation *)
ML \<open>val _ = left_alone (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = x \<and> u \<otimes>\<^bsub>G\<^esub> v = u"\<close>
(* S is not closed by the user's rule -- its q is bound by a binder of the body -- so no
   annotation, although the annotated text would read back as the original *)
ML \<open>val _ = left_alone (on \<^context>) "\<forall>q. x \<otimes>\<^bsub>tmk q\<^esub> y = x"\<close>
(* a binder of the body named like the free H of S: S is closed, the empty subscript sits outside
   the binder, so the text reads back as the original, as stock's explicit text does *)
ML \<open>
val _ = annotated (on \<^context>) "(\<forall>H. Suc H = H) \<and> x \<otimes>\<^bsub>H\<^esub> y = y"
  "(\<forall>H. Suc H = H) \<and> x \<otimes> y = y \<lbrakk>structure: H\<rbrakk>"
\<close>
(* an under-applied inverse is an ordinary argument, no index occurrence: alone nothing is
   annotated, beside a multiplication on H that multiplication's is *)
ML \<open>val _ = left_alone (on \<^context>) "inj_on (m_inv H) (carrier H)"\<close>
ML \<open>
val _ = annotated (on \<^context>) "inj_on (m_inv H) (carrier H) \<and> x \<otimes>\<^bsub>H\<^esub> y = y"
  "inj_on (m_inv H) (carrier H) \<and> x \<otimes> y = y \<lbrakk>structure: H\<rbrakk>"
\<close>
(* three print modes round trip, term and proposition *)
ML \<open>local
val ctxt = on \<^context>;
val p = Syntax.read_prop ctxt "x \<otimes>\<^bsub>H\<^esub> y = y \<otimes>\<^bsub>H\<^esub> x";
val _ = List.app (fn mode =>
    \<^assert> (round_trip_in_mode ctxt Syntax.read_term mode (reads ctxt "x \<otimes>\<^bsub>H\<^esub> y \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub>") andalso
      round_trip_in_mode ctxt Syntax.read_prop mode p))
  ["", "latex", "ASCII"];
in end\<close>
(* a statement whose body fits the margin but not together with the annotation breaks after the
   dot: the annotation and the dot on the first line, the body indented by two on the second *)
ML \<open>local
val ctxt = on \<^context>;
val long = Syntax.read_prop ctxt
  "xaaa \<otimes>\<^bsub>H\<^esub> xbbb \<otimes>\<^bsub>H\<^esub> xccc \<otimes>\<^bsub>H\<^esub> xddd = yggg \<otimes>\<^bsub>H\<^esub> yhhh";
(*the break structure of the prefix template (decision 17): the closing bracket, a break of
  width 0, the dot, a break of width 2, the body -- read off the layout markup of symbolic
  output; and at the default margin the body alone fits while the annotated form breaks*)
fun layout ctxt' t =
  let
    fun tokens (XML.Elem ((name, props), body)) =
          if name = Markup.breakN
          then ["BREAK" ^ the_default "0" (Properties.get props Markup.widthN)]
          else maps tokens body
      | tokens (XML.Text s) = [s];
  in implode (maps tokens (YXML.parse_body (Pretty.symbolic_string_of (Syntax.pretty_term ctxt' t)))) end;
val _ =
  if String.isSubstring "\<rbrakk>BREAK0.BREAK2xaaa" (layout ctxt long) then ()
  else error ("layout tokens: " ^ layout ctxt long);
(*at the default margin the statement does not fit: the first line is the annotation with its
  dot, the second line is indented by two (the body's own breaks are the formatter's)*)
val printed = clean (Print_Mode.setmp [] (Syntax.string_of_term ctxt) long);
val _ =
  (case split_lines printed of
    first :: second :: _ =>
      if first = "\<lbrakk>structure: H\<rbrakk>." andalso String.isPrefix "  xaaa" second then ()
      else error ("prefix form printed as:\n" ^ printed)
  | _ => error ("prefix form printed on one line:\n" ^ printed));
val _ = \<^assert> (round_trip_in_mode ctxt Syntax.read_prop "" long);
in end\<close>

(* the index of a translation-defined \<Otimes> is an index occurrence like the others: mixed with H
   no annotation (the first layer elides G, an empty subscript beside H) *)
ML \<open>val _ = left_alone (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> (\<Otimes>\<^bsub>G\<^esub>i\<in>A. k i i) = z"\<close>
(* where the \<Otimes> print rule does not apply (its body is no abstraction) G is an ordinary
   argument, not an index occurrence: the multiplication's H alone decides and is annotated *)
ML \<open>
val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> finprod G k A = z"
  "x \<otimes> y = y \<and> finprod G k A = z \<lbrakk>structure: H\<rbrakk>"
\<close>
(* the user's example of 2026-10-16 01:18:31 (plan section 4, first row of the AST plan): the
   \<Otimes>'s body is an eta-redex the printer contracts, so its rule does not apply either; the
   output reads back up to eta *)
ML \<open>
val _ = annotated_eta (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> (\<Otimes>\<^bsub>G\<^esub>i\<in>A. k i) = z"
  "x \<otimes> y = y \<and> finprod G k A = z \<lbrakk>structure: H\<rbrakk>"
\<close>
(* all H: the index of the \<Otimes> is elided with the others; where the \<Otimes> print rule does not
   apply the index argument is printed back as H; with the body an eta-redex the printer
   contracts it and the output reads back up to eta *)
ML \<open>
val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> (\<Otimes>\<^bsub>H\<^esub>i\<in>A. k i i) = z"
  "x \<otimes> y = y \<and> (\<Otimes>i\<in>A. k i i) = z \<lbrakk>structure: H\<rbrakk>"
\<close>
ML \<open>
val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> finprod H k A = z"
  "x \<otimes> y = y \<and> finprod H k A = z \<lbrakk>structure: H\<rbrakk>"
\<close>
ML \<open>
val _ = annotated_eta (on \<^context>) "x \<otimes>\<^bsub>H\<^esub> y = y \<and> (\<Otimes>\<^bsub>H\<^esub>i\<in>A. k i) = z"
  "x \<otimes> y = y \<and> finprod H k A = z \<lbrakk>structure: H\<rbrakk>"
\<close>
(* an eta-expanded under-application: the printer contracts it to an ordinary argument, no
   index occurrence, nothing to annotate *)
ML \<open>
val _ = both_modes (fn ctxt => prints_as ctxt "inj_on (\<lambda>x. inv\<^bsub>H\<^esub> x) (carrier H)" "inj_on (m_inv H) (carrier H)")
  (on \<^context>)
\<close>
(* an under-applied multiplication prints by its section rule, its index an index occurrence *)
ML \<open>
val _ = annotated (on \<^context>) "foldr (\<otimes>\<^bsub>H\<^esub>) xs \<one>\<^bsub>H\<^esub> = z"
  "foldr (\<otimes>) xs \<one> = z \<lbrakk>structure: H\<rbrakk>"
\<close>
(* a binder named like the head of the variable structures is not renamed: the empty subscripts
   are put in on the ast, after the printer named the binders *)
ML \<open>val _ = annotated (on \<^context>) "\<forall>G. x \<otimes>\<^bsub>H\<^esub> G = G" "\<forall>G. x \<otimes> G = G \<lbrakk>structure: H\<rbrakk>"\<close>
(* with show_types the annotation's S keeps its type: prune_types gives one copy of S the type --
   the outer multiplication's, in the middle of the printed order -- and the annotation takes the
   copy with the most constraints; the same with the binder of S constrained in every copy, and
   as PIDE prints (show_markup, a constraint on every atom); S a schematic variable likewise *)
ML \<open>local
val ctxt = Config.put show_types true (on \<^context>);
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: tmk (q::"
  (shows ctxt (reads ctxt "x \<otimes>\<^bsub>tmk q\<^esub> y \<otimes>\<^bsub>tmk q\<^esub> z = z \<otimes>\<^bsub>tmk q\<^esub> x")));
in end\<close>
ML \<open>local
val ctxt = Config.put show_types true (on \<^context>);
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: tmk (\<lambda>a::nat. q::int)"
  (shows ctxt (reads ctxt
    "x \<otimes>\<^bsub>tmk (\<lambda>a::nat. q::int)\<^esub> y \<otimes>\<^bsub>tmk (\<lambda>a::nat. q)\<^esub> z = z \<otimes>\<^bsub>tmk (\<lambda>a::nat. q)\<^esub> x")));
in end\<close>
(* copies of S that differ in a binder's type are different structures while types are printed:
   no annotation, the explicit subscripts keep each copy's type and the text reads back *)
ML \<open>local
val ctxt = Config.put show_types true (on \<^context>);
val t = reads ctxt "x \<otimes>\<^bsub>tmk (\<lambda>a::nat. q::int)\<^esub> y \<otimes>\<^bsub>tmk (\<lambda>a. q)\<^esub> z = z \<otimes>\<^bsub>tmk (\<lambda>a. q)\<^esub> x";
val _ = \<^assert> (not (String.isSubstring "structure:" (shows ctxt t)) andalso reads ctxt (shows ctxt t) aconv t);
in end\<close>
ML \<open>local
val ctxt = Config.put show_markup true (Config.put show_types true (on \<^context>));
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: tmk (q::"
  (shows ctxt (reads ctxt "x \<otimes>\<^bsub>tmk q\<^esub> y \<otimes>\<^bsub>tmk q\<^esub> z = z \<otimes>\<^bsub>tmk q\<^esub> x")));
in end\<close>
ML \<open>local
val ctxt = on \<^context>;
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: (?H::"
  (shows (Config.put show_types true ctxt)
    (Term.map_aterms (fn Free ("H", T) => Var (("H", 0), T) | a => a) (reads ctxt "x \<otimes>\<^bsub>H\<^esub> y"))));
in end\<close>
(* a loose bound variable in S (the body of a quantification printed on its own): no annotation *)
ML \<open>local
val ctxt = on \<^context>;
val body =
  (case reads ctxt "\<forall>q. x \<otimes>\<^bsub>tmk q\<^esub> y = x" of
    _ $ Abs (_, _, b) => b
  | t => raise TERM ("no abstraction", [t]));
val s = shows ctxt body;
val _ = \<^assert> (not (String.isSubstring "structure:" s) andalso String.isSubstring "tmk B.0" s);
in end\<close>
(* an index occurrence inside S is not compared: only the outermost ones are, and S is annotated
   as a whole (a compound structure with a subscript of its own, such as HOL-Algebra's K[X]); with
   the first layer's G inside S the first layer elides it to the empty subscript there -- the K[X]
   shape -- and that empty subscript reads back as G *)
ML \<open>
val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>tmk (a \<otimes>\<^bsub>H\<^esub> b)\<^esub> y"
  "x \<otimes> y \<lbrakk>structure: tmk (a \<otimes>\<^bsub>H\<^esub> b)\<rbrakk>"
\<close>
ML \<open>
val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>tmk (a \<otimes>\<^bsub>G\<^esub> b)\<^esub> y" "x \<otimes> y \<lbrakk>structure: tmk (a \<otimes> b)\<rbrakk>"
\<close>
(* S with a binder of its own is closed: its bound a is no bound variable of the body *)
ML \<open>val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>tmk {a. a = a}\<^esub> y" "x \<otimes> y \<lbrakk>structure: tmk {a. a = a}\<rbrakk>"\<close>
(* an empty subscript inside S prints as the first layer's head G beside a binder named G: a name
   coincidence, S is closed and the text reads back as the original *)
ML \<open>
val _ = annotated (on \<^context>) "(\<forall>G. G = G) \<and> x \<otimes>\<^bsub>G\<lparr>one := z\<rparr>\<^esub> y = y"
  "(\<forall>G. G = G) \<and> x \<otimes> y = y \<lbrakk>structure: G\<lparr>one := z\<rparr>\<rbrakk>"
\<close>
(* show_structs on: every subscript is wanted, no annotation *)
ML \<open>val _ = prints_as (Config.put show_structs true (on \<^context>)) "x \<otimes>\<^bsub>H\<^esub> y" "x \<otimes>\<^bsub>H\<^esub> y"\<close>
(* what the uncheck stages expose (AST plan section 6 item 1): with the option on every unchecked
   term is the candidate node; with the option off, or show_structs on, none is *)
ML \<open>local
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes>\<^bsub>H\<^esub> y";
val _ = \<^assert> (unchecks_to_candidate (on ctxt) t);
val _ = \<^assert> (not (unchecks_to_candidate ctxt t));
val _ = \<^assert> (not (unchecks_to_candidate (Config.put show_structs true (on ctxt)) t));
in end\<close>
(* the candidate node is added at the last uncheck stage: a probe at stage 99 never sees it *)
ML \<open>local
val ctxt = on \<^context>;
val probed =
  Context.proof_map
    (Syntax_Phases.term_uncheck 99 "candidate_probe"
      (fn _ => map (fn t => if is_candidate t then error "candidate node before stage 100" else t)))
    ctxt;
val _ = prints_as probed "x \<otimes>\<^bsub>H\<^esub> y" "x \<otimes> y \<lbrakk>structure: H\<rbrakk>";
in end\<close>

(* a proof-fixed p (internal name p__) beside a binder named p (another type): a name
   coincidence again, the printer shows both as p and the text reads back as the original (hol-4
   of the milestone-2 review asked for the explicit subscripts; the name check of decision 17 no
   longer refuses) *)
lemma "True"
proof -
  fix p :: 'q
  ML_prf \<open>
    annotated (on \<^context>) "(\<forall>p. p = p) \<and> x \<otimes>\<^bsub>tmk p\<^esub> y = y"
      "(\<forall>p. p = p) \<and> x \<otimes> y = y \<lbrakk>structure: tmk p\<rbrakk>"
  \<close>
  show True ..
qed
end

(* the quote/antiquote notation hides the binder of assn: the structure sG s prints as \<acute>sG at
   every index occurrence, so the body is annotated, and the text reads back as the original --
   \<acute>sG filled into the subscripts inside \<lbrace> \<rbrace> is turned back into sG s by quote_tr *)
ML \<open>
val _ = annotated (on \<^context>) "assn (\<lambda>s. x \<otimes>\<^bsub>sG s\<^esub> y = y)"
  "\<lbrace>x \<otimes> y = y\<rbrace> \<lbrakk>structure: \<acute>sG\<rbrakk>"
\<close>

(* two stock structure variables, G first, a fixed variable with index syntax and the nested
   index syntax BAR: the index of each kind is an index occurrence -- mixed with H no annotation
   (and the first layer elides G), all H annotated with every subscript elided *)
context
  fixes G :: "'a monoid" (structure) and H :: "'a monoid" (structure)
    and F :: "'a monoid \<Rightarrow> 'a \<Rightarrow> 'a" (\<open>\<Phi>\<index> _\<close> [1000] 999)
    and x y :: 'a
begin
ML \<open>val _ = \<^assert> (layers (on \<^context>) = (SOME "G", NONE))\<close>
ML \<open>val _ = left_alone (on \<^context>) "\<Phi>\<^bsub>G\<^esub> x = x \<otimes>\<^bsub>H\<^esub> y"\<close>
ML \<open>val _ = annotated (on \<^context>) "\<Phi>\<^bsub>H\<^esub> x = x \<otimes>\<^bsub>H\<^esub> y" "\<Phi> x = x \<otimes> y \<lbrakk>structure: H\<rbrakk>"\<close>
ML \<open>val _ = left_alone (on \<^context>) "bar (baz G) x = x \<otimes>\<^bsub>H\<^esub> y"\<close>
ML \<open>val _ = annotated (on \<^context>) "bar (baz H) x = x \<otimes>\<^bsub>H\<^esub> y" "BAR x = x \<otimes> y \<lbrakk>structure: H\<rbrakk>"\<close>
(* BAR's rule does not apply (G in place of baz G): G is an ordinary argument and prints as
   itself *)
ML \<open>val _ = annotated (on \<^context>) "bar G x = x \<otimes>\<^bsub>H\<^esub> y" "bar G x = x \<otimes> y \<lbrakk>structure: H\<rbrakk>"\<close>
(* the same with bar under-applied *)
ML \<open>val _ = annotated (on \<^context>) "bar G = (\<lambda>z. z \<otimes>\<^bsub>H\<^esub> y)" "bar G = (\<lambda>z. z \<otimes> y) \<lbrakk>structure: H\<rbrakk>"\<close>
(* an abstraction the printer eta-contracts, after which BAR2's rule applies: with G there the
   first layer elides it and the empty subscript beside H refuses; with H there every index
   occurrence is H and the body is annotated; both outputs read back up to eta *)
ML \<open>local
val ctxt = on \<^context>;
val t = reads ctxt "bar2 (\<lambda>z. baz2 G z) x = x \<otimes>\<^bsub>H\<^esub> y";
val _ = \<^assert> (shows ctxt t = "BAR2 x = x \<otimes>\<^bsub>H\<^esub> y" andalso Envir.aeconv (reads ctxt (shows ctxt t), t));
in end\<close>
ML \<open>
val _ = annotated_eta (on \<^context>) "bar2 (\<lambda>z. baz2 H z) x = x \<otimes>\<^bsub>H\<^esub> y"
  "BAR2 x = x \<otimes> y \<lbrakk>structure: H\<rbrakk>"
\<close>
end

(* a second layer whose value holds an eta-redex: Pure's own elision compares the terms before
   the printer eta-contracts, so the subscript is already the empty subscript when the decision
   is made -- the default structure, no annotation *)
context
begin
set_implicit_structure "\<lparr>carrier = {x. True}, mult = \<lambda>a b. a + b, one = 0\<rparr> :: int monoid"
ML \<open>val _ = both_modes (fn ctxt => (prints_as ctxt "x \<otimes> y" "x \<otimes> y"; left_alone ctxt "x \<otimes> y")) (on \<^context>)\<close>
end

(* a second-layer value holding an abbreviation (UNIV for top): Pure's elision compares the
   stored value put through the uncheck stages, where the abbreviation folds as it does in the
   printed term, so the subscript is the empty subscript as well -- the default structure, no
   annotation (section 11 (39)) *)
context
begin
set_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
ML \<open>val _ = both_modes (fn ctxt => (prints_as ctxt "x \<otimes> y" "x \<otimes> y"; left_alone ctxt "x \<otimes> y")) (on \<^context>)\<close>
context fixes k :: nat begin
(*an index differing from the second layer only in its type is another structure: annotated,
  read back on nat*)
ML \<open>
val _ = annotated (on \<^context>) "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\<^esub> = k"
  "\<one> = k \<lbrakk>structure: \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\<rbrakk>"
\<close>
end
end

(* both layers empty: an under-applied inverse with the option on leaks nothing *)
ML \<open>local
val ctxt = on \<^context>;
val t = reads ctxt "inj_on (m_inv W) (carrier W)";
val _ = \<^assert> (not (String.isSubstring "_struct" (shows ctxt t)) andalso not (has_bad_markup ctxt t));
in end\<close>

(* both layers present (M1: S is the first layer, f S the second): the first layer's head is
   printed, not elided, so a subscript S is another structure than the default and is annotated;
   the second layer's value is elided by Pure and is the default *)
context M1
begin
ML \<open>val _ = \<^assert> (#1 (layers \<^context>) = SOME "S" andalso implicit_is \<^context> (reads \<^context> "f S"))\<close>
ML \<open>val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>S\<^esub> y" "x \<otimes> y \<lbrakk>structure: S\<rbrakk>"\<close>
ML \<open>val _ = both_modes (fn ctxt => prints_as ctxt "x \<otimes>\<^bsub>f S\<^esub> y" "x \<otimes> y") (on \<^context>)\<close>
ML \<open>val _ = left_alone (on \<^context>) "x \<otimes>\<^bsub>S\<^esub> y = x \<and> u \<otimes> v = u"\<close>
end

(* the second layer as the default (UP S): S is another structure and gets the annotation, a
   translation-defined \<Oplus> on S elided with the rest; the default itself is not annotated -- Pure
   elides v at every index position, the \<Oplus> included, and the placeholder by name, so the
   decision sees only the empty subscript -- and mixed with S no annotation; the under-applied
   inverse on S reads back; with show_types the annotation's S keeps its type *)
context LF
begin
ML \<open>val _ = both_modes (fn ctxt => prints_as ctxt "x \<otimes>\<^bsub>UP S\<^esub> y" "x \<otimes> y") (on \<^context>)\<close>
ML \<open>val _ = annotated (on \<^context>) "x \<otimes>\<^bsub>S\<^esub> y" "x \<otimes> y \<lbrakk>structure: S\<rbrakk>"\<close>
ML \<open>val _ = \<^assert> (round_trips (on \<^context>) (reads \<^context> "inj_on (m_inv S) (carrier S)"))\<close>
ML \<open>
val _ = annotated (on \<^context>) "(\<Oplus>\<^bsub>S\<^esub>i\<in>A. u i \<otimes>\<^bsub>S\<^esub> v i) = w"
  "(\<Oplus>i\<in>A. u i \<otimes> v i) = w \<lbrakk>structure: S\<rbrakk>"
\<close>
ML \<open>val _ = left_alone (on \<^context>) "x \<otimes>\<^bsub>S\<^esub> y = y \<and> (\<Oplus>\<^bsub>UP S\<^esub>i\<in>A. p i i) = q"\<close>
ML \<open>val _ = left_alone (on \<^context>) "(\<Oplus>\<^bsub>UP S\<^esub>i\<in>A. p i i) = q"\<close>
ML \<open>local
val ctxt = Config.put show_types true (on \<^context>);
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: (S::" (shows ctxt (reads ctxt "x \<otimes>\<^bsub>S\<^esub> y")));
in end\<close>
(* the placeholder at the \<Oplus>'s index, as a term printed before the check stage replaces it (a type
   error message): Pure elides the placeholder by name, so the decision sees the empty subscript *)
ML \<open>local
val ctxt = on \<^context>;
val value = reads ctxt "UP S";
val t =
  Term.subst_free [(value, Free (Syntax_Trans.implicit_structure_, fastype_of value))]
    (reads ctxt "(\<Oplus>\<^bsub>UP S\<^esub>i\<in>A. p i i) = q");
val _ = \<^assert> (has_placeholder t andalso not (String.isSubstring "structure:" (shows ctxt t)));
in end\<close>
(* S a schematic variable beside a second layer: the comparison with the default structure must
   not reject it (expand_abbrevs would) *)
ML \<open>local
val ctxt = on \<^context>;
val _ = \<^assert> (String.isSubstring "\<lbrakk>structure: ?S\<rbrakk>"
  (shows ctxt (Term.map_aterms (fn Free ("S", T) => Var (("S", 0), T) | a => a) (reads ctxt "x \<otimes>\<^bsub>S\<^esub> y"))));
in end\<close>
end


subsection \<open>An interpret leaves the two layers alone (plan 5274-5279)\<close>

context LF
begin
lemma
  fixes S' :: "('a, 'b) ring_scheme"
  assumes c: "cring S'"
  shows True
proof -
  ML_prf \<open>val layers0 = layers \<^context>\<close>
  interpret I: LF S' using c unfolding LF_def UP_cring_def .
  ML_prf \<open>
    val layers1 = layers \<^context>;
    val _ = \<^assert> (#1 layers1 = #1 layers0 andalso #1 layers1 = NONE);
    val _ = \<^assert> (is_some (#2 layers1) andalso the (#2 layers1) aconv the (#2 layers0) andalso
      implicit_is \<^context> (reads \<^context> "UP S"));
  \<close>
  show True ..
qed
end

end
