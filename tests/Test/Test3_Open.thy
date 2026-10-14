(* Plan section 7 test 3 (opening), the rows on the gate fixture that change no persistent theory
   state: what context LF begin and Locale.init LF provide, the performance rows, and the
   record-only remedy row on LFc. *)
theory Test3_Open
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>
fun visible_facts ctxt =
  Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
    (Proof_Context.facts_of ctxt)
  |> map #1 |> sort_strings;

fun local_consts ctxt =
  let val global = map #1 (#constants (Consts.dest (Sign.consts_of (Proof_Context.theory_of ctxt))))
  in subtract (op =) global (map #1 (#constants (Consts.dest (Proof_Context.consts_of ctxt)))) end;

(*the predicate fact LF_axioms and the _axioms fact of every closure instance*)
val lf_facts =
  "local.LF_axioms" ::
  map (prefix "local.")
   (maps (fn q => map (prefix q)
      ["abelian_group_axioms", "abelian_monoid_axioms", "add.comm_group_axioms",
       "add.comm_monoid_axioms", "add.group_axioms", "add.monoid_axioms", "comm_monoid_axioms",
       "cring_axioms", "monoid_axioms", "ring_axioms", "semiring_axioms"]) ["P.", "R."] @
    ["UP_cring_axioms", "UP_ring_axioms", "algebra_axioms", "module_axioms"])
  |> sort_strings;

val D_ctxt = Locale.init (Locale.check_global \<^theory> ("D", Position.none)) \<^theory>;
\<close>

context LF begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Variable.dest_fixes ctxt = [("S", "S")]);
val _ = \<^assert> (map Thm.prop_of (Assumption.all_prems_of ctxt) = [@{prop "LF S"}]);
(*first layer: S is re-fixed without a mark*)
val _ = \<^assert> (is_none (Syntax_Trans.default_struct ctxt));
val _ = \<^assert> (local_consts ctxt = local_consts D_ctxt);
val _ = \<^assert> (visible_facts ctxt = lf_facts);
(*short-name theorems and the heavy head assumptions are absent; the heavy twin has them*)
fun has_fact ctxt name = can (Proof_Context.get_fact ctxt) (Facts.named name);
val _ = \<^assert> (forall (has_fact D_ctxt) ["R.m_comm", "P.m_comm", "UP_cring.intro", "R.is_cring"]);
val _ = \<^assert> (not (exists (has_fact ctxt) ["R.m_comm", "P.m_comm", "R.is_cring", "m_comm"]));
\<close>
end

(* Locale.init LF: the heavy theorem names are absent as well *)
ML \<open>
val lf_ctxt = Locale.init (Locale.check_global \<^theory> ("LF", Position.none)) \<^theory>;
val _ = \<^assert> (visible_facts lf_ctxt = lf_facts);
\<close>

(* performance: every heavy locale of the closure has a note with a non-empty binding, so the fact
   names above imply that no closure instance was fully activated; the written closure instances
   carry only the Syntax_only mark; the closure size is recorded only *)
ML \<open>
val thy = \<^theory>;
val lf = Locale.check_global thy ("LF", Position.none);
val closure = ["UnivPoly.UP_cring", "UnivPoly.UP_ring", "Ring.cring", "Ring.ring",
  "Ring.abelian_group", "Ring.abelian_monoid", "Ring.semiring", "Group.monoid",
  "Group.comm_monoid", "Group.group", "Group.comm_group", "Module.module", "Module.algebra"];
val _ = \<^assert> (forall (fn loc =>
  exists (exists (not o Binding.is_empty o #1 o #1) o #2) (Locale.locale_notes thy loc)) closure);
val S = @{term "S :: ('a, 'b) ring_scheme"};
val instances =
  [("UnivPoly.UP_cring", [S, @{term "UP S"}]), ("Ring.cring", [S]), ("Ring.cring", [@{term "UP S"}]),
   ("Module.algebra", [S, @{term "UP S"}])];
val marks = map (Locale.matching_marks_of (Context.Proof lf_ctxt)) instances;
val _ = \<^assert> (forall (fn ((_, ts), recs) =>
    (case recs of
      [(ts', Locale.Syntax_only, _)] => eq_list (op aconv) (ts, ts')
    | _ => false)) (instances ~~ marks));
val _ = writeln ("closure dependencies: " ^ string_of_int (length (Locale.dest_dependencies [] thy)));

(*a loose upper bound on the opening time relative to the heavy twin; absolute times recorded*)
fun time f = #elapsed (Timing.result (Timing.start () |> tap (fn _ => f ())));
fun open_time loc = time (fn () => Locale.init (Locale.check_global thy (loc, Position.none)) thy);
val light_time = open_time "LF" and heavy_time = open_time "D";
val _ = writeln ("opening LF: " ^ Time.toString light_time ^ "s, D: " ^ Time.toString heavy_time ^ "s");
(*measured 2026-10-13: 0.014s against 0.128s*)
val _ = \<^assert> (Time.toReal light_time < 0.5 * Time.toReal heavy_time);
\<close>

(* record only (not a gate row): the remedy for referring to a fact by its statement; the nested
   block's head elements are activated in statement mode and enter the index by statement *)
light_locale LFc = fixes S :: "nat set" assumes fin: "finite S"

context LFc begin
ML \<open>val facts_before = map #1 (Facts.dest_static false [] (Global_Theory.facts_of \<^theory>))\<close>
context notes fin = LFc.fin[OF LFc_axioms] begin
lemma "finite S" by (rule \<open>finite S\<close>)
end
ML_val \<open>
\<^assert> (map #1 (Facts.dest_static false [] (Global_Theory.facts_of \<^theory>)) = facts_before)
\<close>
end

end
