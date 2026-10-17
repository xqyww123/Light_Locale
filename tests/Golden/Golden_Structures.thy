(* Plan section 7 test 9: three kinds of golden line, each "label, tab, text": the printed form
   of terms whose every index is explicit, printed at the theory level -- no default structure --
   where stock prints each index (plan 3942-3944); print_context's structures line of a block
   with one variable structure, as text and as the markup tree of symbolic output (plan
   5311-5314); and the assumption Child records, rendered without the printer (plan 5132-5134).
   Test 9 reads them as the expected values of the light rows that must match stock byte for
   byte. *)
theory Golden_Structures
  imports "HOL-Algebra.UnivPoly"
begin

ML_file "golden.ML"

consts f :: "('a, 'b) monoid_scheme \<Rightarrow> ('a, 'b) monoid_scheme"

locale A = fixes G :: "('a, 'b) monoid_scheme" (structure)

(* test 9's sublocale pin (plan 5132-5134): Child's recorded assumption *)
locale Mid = fixes G :: "('a, 'b) monoid_scheme" (structure) and R' :: "('c, 'd) ring_scheme"
sublocale Mid \<subseteq> UP R' "UP R'" by simp
locale Child = Mid + fixes x y assumes c: "x \<otimes> y = y \<otimes> x"

ML \<open>
val ctxt = \<^context>;
(*one line each: printed with a wide margin, no print mode*)
fun line (label, text) =
  label ^ "\t" ^
    XML.content_of (YXML.parse_body
      (Print_Mode.setmp []
        (Pretty.string_of_ops (Pretty.output_ops (SOME 1000)) o Syntax.pretty_term ctxt)
        (Syntax.read_term ctxt text)));
(*print_context's structures line of a block with one variable structure: its text, and its
  markup tree as symbolic output prints it*)
val structures_line =
  hd (Proof_Context.pretty_ctxt (Config.put Proof_Context.debug true
    (Locale.init (Locale.check_global \<^theory> ("A", Position.none)) \<^theory>)));
val structures_A =
  "structures_A\t" ^ XML.content_of (YXML.parse_body (Print_Mode.setmp [] Pretty.string_of structures_line));
val structures_A_markup =
  "structures_A_markup\t" ^
    XML.string_of (XML.Elem (("line", []), YXML.parse_body (Pretty.symbolic_string_of structures_line)));
(*Child's assumption, rendered without the printer*)
val child_assumption =
  "Child_assumption\t" ^
    ML_Syntax.print_term (#1 (hd (#2 (hd (maps (fn Element.Assumes asms => asms | _ => [])
      (Locale.hyp_spec_of \<^theory> (Locale.check_global \<^theory> ("Child", Position.none))))))));
val _ =
  Golden.check \<^theory> "structures.golden" (cat_lines (structures_A :: structures_A_markup :: child_assumption :: map line
    [("otimes_G", "x \<otimes>\<^bsub>G\<^esub> y"),
     ("otimes_S", "x \<otimes>\<^bsub>S\<^esub> y"),
     ("otimes_T", "x \<otimes>\<^bsub>T\<^esub> y"),
     ("otimes_UP_S", "x \<otimes>\<^bsub>UP S\<^esub> y"),
     ("otimes_UP_R", "x \<otimes>\<^bsub>UP R\<^esub> y"),
     ("otimes_f_S", "x \<otimes>\<^bsub>f S\<^esub> y"),
     ("finsum_G", "\<Oplus>\<^bsub>G\<^esub>i\<in>A. u i \<otimes>\<^bsub>G\<^esub> v i"),
     ("one_int_monoid",
      "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\<^esub> = (k :: nat)"),
     ("UP_S", "UP S")]) ^ "\n");
\<close>

end
