(*  Plan section 7 test 1 (invariance): byte-for-byte reference output.

    The tree decides the mode: on light's stock tree -- the tree without light, migration plan
    section 7, whose ISABELLE_IDENTIFIER is its directory name <release>-light_locale-stock -- a
    check records tests/golden/<name>; on any other tree it compares and, on a mismatch, writes
    tests/golden/<name>.actual next to the reference and fails.  Theorems are rendered with
    ML_Syntax.print_term so that the facts tables do not depend on the printer, which is itself
    under test (the locale dumps are the printer's tripwire).
*)

signature GOLDEN =
sig
  val recording: bool
  val check: theory -> string -> string -> unit
  val thms_dump: (string * thm) list -> string
  val facts_dump: theory -> string -> string
  val locales_dump: theory -> string list -> string
end;

structure Golden: GOLDEN =
struct

val recording = String.isSuffix "-light_locale-stock" (getenv "ISABELLE_IDENTIFIER");

fun golden_dir thy = Path.append (Resources.master_directory thy) (Path.explode "../golden");

fun first_difference expected actual =
  let
    val ls1 = split_lines expected and ls2 = split_lines actual;
    fun find i (l1 :: r1) (l2 :: r2) = if l1 = l2 then find (i + 1) r1 r2 else SOME (i, l1, l2)
      | find _ [] [] = NONE
      | find i (l1 :: _) [] = SOME (i, l1, "<end of actual>")
      | find i [] (l2 :: _) = SOME (i, "<end of golden>", l2);
  in
    (case find 1 ls1 ls2 of
      SOME (i, l1, l2) =>
        "line " ^ string_of_int i ^ "\n  golden: " ^ l1 ^ "\n  actual: " ^ l2 ^
        "\n  (" ^ string_of_int (length ls1) ^ " vs " ^ string_of_int (length ls2) ^ " lines)"
    | NONE => "no line differs (trailing newline?)")
  end;

fun check thy name text =
  let
    val dir = golden_dir thy;
    val path = Path.append dir (Path.basic name);
  in
    if recording then
      (Isabelle_System.make_directory dir; File.write path text;
       writeln ("recorded golden " ^ name ^ " (" ^ string_of_int (size text) ^ " bytes)"))
    else
      let val expected = File.read path in
        if expected = text then writeln ("golden " ^ name ^ " matches")
        else
          (File.write (Path.append dir (Path.basic (name ^ ".actual"))) text;
           error ("golden " ^ name ^ " differs at " ^ first_difference expected text ^
             "\n  actual output written next to it as " ^ name ^ ".actual"))
      end
  end;

(* the statement is kept as the SHA1 of its ML_Syntax rendering: the full text of HOL-Algebra's
   facts is 62MB; on a mismatch the .actual file names the theorem and both sides can be
   re-rendered in full *)
fun thm_entry (name, th) =
  name ^ "  " ^ SHA1.rep (SHA1.digest (ML_Syntax.print_term (Thm.prop_of th))) ^
  "  nprems=" ^ string_of_int (Thm.nprems_of th) ^
  " tags=" ^ commas (map (fn (k, v) => k ^ "=" ^ v) (sort_by #1 (Thm.get_tags th)));

fun thms_dump named = cat_lines (map thm_entry named) ^ "\n";

fun indexed (name, [th]) = [(name, th)]
  | indexed (name, ths) = map_index (fn (i, th) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", th)) ths;

(* every fact first stated in an ancestor theory whose long name has the prefix, by theory then by
   name.  Ancestors, not Thy_Info: theories loaded in the running session are not registered there
   yet (the corec dump came out empty) *)
fun facts_dump thy prefix =
  Theory.ancestors_of thy
  |> filter (String.isPrefix prefix o Context.theory_long_name)
  |> sort (string_ord o apply2 Context.theory_long_name)
  |> maps (fn thy' =>
      let
        val new_facts =
          Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy'))
            (Global_Theory.facts_of thy')
          |> sort_by #1 |> maps indexed;
      in
        ("## " ^ Context.theory_long_name thy' ^ " (" ^ string_of_int (length new_facts) ^ " theorems)")
          :: map thm_entry new_facts
      end)
  |> cat_lines |> suffix "\n";

fun locales_dump thy names =
  cat_lines (map (fn name =>
    Print_Mode.setmp [] (fn () => Pretty.string_of (Locale.pretty_locale thy true name)) ()
    |> YXML.parse_body |> XML.content_of) names) ^ "\n";

end;
