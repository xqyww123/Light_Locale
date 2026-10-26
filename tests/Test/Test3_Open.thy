(* Plan section 7 test 3 (opening), the rows on the gate fixture that change no persistent theory
   state: what context LF begin and Locale.init LF provide, the performance rows, and the evidence
   row on LFc (plan 4031: record only; pinned to the outcome measured on stock). *)
theory Test3_Open
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>
open Test_Support;

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
ML \<open>local
val ctxt = \<^context>;
(*S and, since milestone 2, the placeholder of the implicit structure under its literal name --
  nothing else; the second layer is UP S (plan 4022)*)
val _ = \<^assert> (Variable.dest_fixes ctxt =
  [("S", "S"), (Syntax_Trans.implicit_structure_, Syntax_Trans.implicit_structure_)]);
val _ = \<^assert> (implicit_is ctxt (reads ctxt "UP S"));
val _ = \<^assert> (map Thm.prop_of (Assumption.all_prems_of ctxt) = [@{prop "LF S"}]);
(*first layer: S is re-fixed without a mark*)
val _ = \<^assert> (is_none (Syntax_Trans.default_struct ctxt));
val _ = \<^assert> (local_consts ctxt = local_consts D_ctxt);
val _ = \<^assert> (visible_fact_names ctxt = lf_facts);
(*the heavy twin (plan 4047-4048): its visible set contains every one of these and more -- the
  short-name theorems and the heavy head assumptions, which the light block does not have*)
val heavy_only = ["R.m_comm", "P.m_comm", "R.is_cring", "m_comm"];
val _ = \<^assert> (subset (op =) (remove (op =) "local.LF_axioms" lf_facts, visible_fact_names D_ctxt));
val _ = \<^assert> (forall (has_fact D_ctxt) heavy_only);
val _ = \<^assert> (not (exists (has_fact ctxt) heavy_only));
in end\<close>
end

(* Locale.init LF: the heavy theorem names are absent as well *)
ML \<open>
val lf_ctxt = Locale.init (Locale.check_global \<^theory> ("LF", Position.none)) \<^theory>;
val _ = \<^assert> (visible_fact_names lf_ctxt = lf_facts);
\<close>

(* performance (plan 4048-4051): the closure instances of LF, every (locale, instance) reached from
   LF over the dependency edges, morphisms composed along the path, mixins ignored; the closure
   size is recorded only.  Every heavy locale of the closure has a named, not concealed note other
   than its <loc>_axioms predicate note (the Light selection installs that note too, and concealed
   names are invisible to visible_fact_names), so the fact names above imply that no closure
   instance was fully activated; the written closure instances carry only the Syntax_only mark *)
ML \<open>
val thy = \<^theory>;
val lf = Locale.check_global thy ("LF", Position.none);
fun closure_instances name =
  let
    val deps = Locale.dest_dependencies [] thy;
    fun same (n, ts) (n', ts') = n = n' andalso eq_list (op aconv) (ts, ts');
    fun visit (n, m) seen =
      let val inst = (n, Locale.instance_of thy n m) in
        if exists (same inst) seen then seen
        else
          fold (fn {source, target, morphism, ...} => target = n ? visit (source, morphism $> m))
            deps (inst :: seen)
      end;
  in visit (name, Morphism.identity) [] end;
val insts = closure_instances lf;
val _ = writeln ("closure instances of LF: " ^ string_of_int (length insts));
fun named_note loc ((b, _), _) =
  not (Binding.is_empty b) andalso not (#concealed (Binding.name_spec [] [] b))
  andalso Binding.name_of b <> Long_Name.base_name loc ^ "_axioms";
val _ = \<^assert> (forall (fn loc => exists (exists (named_note loc) o #2) (Locale.locale_notes thy loc))
  (remove (op =) lf (distinct (op =) (map #1 insts))));
val S = @{term "S :: ('a, 'b) ring_scheme"};
val instances =
  [("UnivPoly.UP_cring", [S, @{term "UP S"}]), ("Ring.cring", [S]), ("Ring.cring", [@{term "UP S"}]),
   ("Module.algebra", [S, @{term "UP S"}])];
val marks = map (Locale.matching_marks_of (Context.Proof lf_ctxt)) instances;
val _ = \<^assert> (forall (fn ((_, ts), recs) =>
    (case recs of
      [(ts', Locale.Syntax_only, _)] => eq_list (op aconv) (ts, ts')
    | _ => false)) (instances ~~ marks));

(*a loose upper bound on the opening time relative to the heavy twin; absolute times recorded*)
fun time f = #elapsed (Timing.result (Timing.start () |> tap (fn _ => f ())));
fun open_time loc = time (fn () => Locale.init (Locale.check_global thy (loc, Position.none)) thy);
val light_time = open_time "LF" and heavy_time = open_time "D";
val _ = writeln ("opening LF: " ^ Time.toString light_time ^ "s, D: " ^ Time.toString heavy_time ^ "s");
(*measured 2026-10-13: 0.014s against 0.128s*)
val _ = \<^assert> (Time.toReal light_time < 0.5 * Time.toReal heavy_time);
\<close>

(* evidence (plan 4031: record only), pinned to the outcome measured on stock
   (Round25_Stock_Probe.thy (5)); a mismatch is re-measured, not bug-hunted: the remedy for
   referring to a fact by its statement; the nested block's head elements are activated in
   statement mode and enter the index by statement *)
light_locale LFc = fixes S :: "nat set" assumes fin: "finite S"

context LFc begin
ML \<open>val facts_before = map #1 (Facts.dest_static false [] (Global_Theory.facts_of \<^theory>))\<close>
context notes fin = LFc.fin[OF LFc_axioms] begin
lemma "finite S" by (rule \<open>finite S\<close>)
end
ML \<open>
val _ = \<^assert> (map #1 (Facts.dest_static false [] (Global_Theory.facts_of \<^theory>)) = facts_before)
\<close>
end

end
