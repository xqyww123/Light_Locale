(* A Lifting setup made in the block of a light locale with assumptions is stored at theory level
   with the locale's predicate as the one premise of its quotient theorem, pcrel definition and
   pcr_cr_eq, K = 1 (plan ai-artifacts/LIGHT_LOCALE_TAT_INTERFACE_PLAN.md section 5 row E), as
   Lifting_Info.lookup_quotients and Lifting_Info.lookup_restore_data return it.  Outside the
   declaring block the readers that prove with it refuse with one sentence (plan
   ai-artifacts/LIGHT_LOCALE_LIFTING_OUTSIDE_PLAN.md section 5): lift_definition, includes,
   lifting_restore, lift_bnf.  In the block of a light locale importing LQ, after an
   interpretation of LQ and in the reopened declaring block the predicate is a fact: the repair
   phase's second step is to discharge the premise there, so the rows asserting K = 1 or the
   sentence there are the ones it changes. *)
theory Test8_Lifting_Premise
  imports Test_Support
begin

(* the relation may not mention the parameter (quotient_type: "illegal variable(s) in the
   relation"); the premise comes from the block's assumption all the same *)
light_locale LQ = fixes n :: nat assumes pos: "0 < n"
begin
quotient_type qt = nat / "\<lambda>x y. x mod 2 = y mod 2"
  by (auto intro!: equivpI reflpI sympI transpI)
quotient_type 'a pq = "'a list" / "\<lambda>xs ys. length xs = length ys"
  by (auto intro!: equivpI reflpI sympI transpI)
(* O6: the declaring block serves *)
lift_definition z0 :: qt is "1 :: nat" .
end

ML \<open>
(*the key of a setup's restore data: the string in its bundle's one attribute, which includes and
  TAT's LiftingContext follow (lifting_setup.ML's pointer_of_bundle_name, not exported).  For a
  setup made in a block it is not the bundle's name: Test8_Lifting_Premise.qt.lifting against
  Test8_Lifting_Premise.LQ.qt.lifting, in a heavy locale block alike.*)
fun restore_key ctxt bundle =
  (case Test_Support.bundle_of ctxt bundle of
    [(_, [src])] => Token.read ctxt Parse.string src
  | _ => raise Fail "not a lifting bundle");
fun restore_quotient ctxt =
  #quotient
    (the (Lifting_Info.lookup_restore_data ctxt (restore_key ctxt "LQ.qt.lifting")));
(*the quotient theorem, pcrel definition and pcr_cr_eq of qt as Lifting_Info.lookup_quotients and
  Lifting_Info.lookup_restore_data return them: K, the setclass premises, all premises*)
fun premise_counts ctxt =
  let
    fun counts th =
      (Setclass.count_of th, length (Test_Support.light_prems ctxt th),
        length (Thm.prems_of th));
    fun three ({quot_thm, pcr_info = SOME {pcrel_def, pcr_cr_eq}}: Lifting_Info.quotient) =
          (counts quot_thm, counts pcrel_def, counts pcr_cr_eq)
      | three _ = raise Fail "no pcr_info";
  in
    (three (the (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>LQ.qt\<close>)),
      three (restore_quotient ctxt))
  end;
val all_one = ((1, 1, 1), (1, 1, 1), (1, 1, 1));
\<close>

(* K = 1 at theory level: the predicate is no fact here, before and after the second step *)
ML \<open>val _ = \<^assert> (premise_counts \<^context> = (all_one, all_one))\<close>

light_locale LQ_user = LQ
begin
(* K = 1 in the block today; the repair phase's second step discharges the premise here *)
ML \<open>val _ = \<^assert> (premise_counts \<^context> = (all_one, all_one))\<close>
end

light_locale Other = fixes m :: nat assumes posm: "0 < m"

(* the heavy twin: its theorems carry the predicate with K = 0, Lifting's own behaviour stays *)
locale HQ = fixes n :: nat assumes hpos: "0 < n"
begin
quotient_type hq = nat / "\<lambda>x y. x mod 5 = y mod 5"
  by (auto intro!: equivpI reflpI sympI transpI)
end

ML \<open>
(*the sentence from its two slots*)
fun only_in ty loc =
  "You can only use the lifting of `" ^ ty ^ "` in the `" ^ loc ^ "` locale, a locale extending " ^
    "it, or a theory where such a locale is installed by an interpretation.";
fun lift_def (name, typ, rhs) lthy =
  Lifting_Def_Code_Dt.lift_def_cmd ([], (Binding.name name, SOME typ, NoSyn), rhs, []) lthy;
fun includes thy bundle =
  Target_Context.context_begin_nested_cmd [((true, Position.none), (bundle, Position.none))] []
    (Context.Theory thy);
fun block thy l = Named_Target.init [] (Test_Support.loc thy l) thy;
fun raises_TERM f = (case Exn.capture f () of Exn.Exn (TERM _) => true | _ => false);
fun pcr_qt_rules ctxt =
  filter (exists_Const (fn (c, _) => c = \<^const_name>\<open>LQ.pcr_qt\<close>) o Thm.prop_of)
    (Transfer.get_transfer_raw ctxt);
fun registered ctxt = is_some (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>LQ.qt\<close>);
fun refuses text f = (Test_Support.fails_with text f; true);
val sanity = "Sanity check of the quotient theorem failed:";

val thy = \<^theory>;
val ctxt = \<^context>;
val key = restore_key ctxt "LQ.qt.lifting";
val interpreted = Test_Support.interpretation_cmd "LQ 1" thy;
(*O12: K = 1 on a premise that is no light predicate, as in a nested assumes block (quotient_type
  cannot be made there, heavy and light alike)*)
val hq = #quot_thm (the (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>HQ.hq\<close>));
val unpredicated = Setclass.put 1 (Local_Defs.unfold0 ctxt @{thms HQ_def} hq);
val with_unpredicated =
  Context.proof_map (Lifting_Info.update_quotients \<^type_name>\<open>HQ.hq\<close>
    {quot_thm = unpredicated, pcr_info = NONE});

val _ = Test_Support.check_rows [
  ("O1", fn () => refuses (only_in "LQ.qt" "LQ")
    (fn () => lift_def ("z1", "LQ.qt", "0 :: nat") (Named_Target.theory_init thy))),
  ("O1b", fn () => refuses (only_in "LQ.qt" "LQ")
    (fn () => lift_def ("p1", "LQ.qt => LQ.qt => LQ.qt", "(+)") (Named_Target.theory_init thy))),
  ("O1c", fn () => refuses (only_in "LQ.qt" "LQ")
    (fn () => lift_def ("u1", "LQ.qt", "undefined") (Named_Target.theory_init thy))),
  ("O2", fn () => refuses (only_in "LQ.qt" "LQ")
    (fn () => lift_def ("z2", "LQ.qt", "0 :: nat") (block thy "Other"))),
  ("O3", fn () => refuses (only_in "LQ.qt" "LQ") (fn () => includes thy "LQ.qt.lifting")),
  ("O3 restore", fn () => refuses (only_in "LQ.qt" "LQ")
    (fn () => Lifting_Setup.lifting_restore (restore_quotient ctxt) (Context.Proof ctxt))),
  ("O4", fn () => refuses (only_in "qt" "LQ")
    (fn () => lift_def ("z4", "qt", "0 :: nat") (block thy "LQ_user"))),
  ("O5", fn () => refuses (only_in "qt" "LQ")
    (fn () => lift_def ("z5", "LQ.qt", "0 :: nat") (Named_Target.theory_init interpreted))),
  ("O5b", fn () => refuses (only_in "qt" "LQ")
    (fn () => lift_def ("z9", "qt", "0 :: nat") (block thy "LQ"))),
  ("O9", fn () =>
    Lifting_Util.concl_rty_qty (#quot_thm (restore_quotient ctxt)) =
      (\<^typ>\<open>nat\<close>, \<^typ>\<open>LQ.qt\<close>)),
  (*O11: the readers that take the type's name or the correspondence relation from the
    conclusion: lifting_update then lifting_forget, on a throw-away local theory*)
  ("O11", fn () =>
    let
      val lthy = Named_Target.theory_init thy;
      val forgotten =
        lthy |> Lifting_Setup.update_transfer_rules key |> Lifting_Setup.lifting_forget key;
    in
      registered lthy andalso not (null (pcr_qt_rules lthy)) andalso
        not (registered forgotten) andalso null (pcr_qt_rules forgotten)
    end),
  (*restore data without pcr_info: lifting_forget takes the correspondence relation from the
    conclusion (lifting_setup.ML get_transfer_rel)*)
  ("O11 crel", fn () =>
    let
      val lthy =
        Context.proof_map (Lifting_Info.init_restore_data key
          {quot_thm = #quot_thm (restore_quotient ctxt), pcr_info = NONE})
          (Named_Target.theory_init thy);
    in registered lthy andalso not (registered (Lifting_Setup.lifting_forget key lthy)) end),
  ("O10", fn () => refuses (only_in "LQ.pq" "LQ")
    (fn () =>
      BNF_Lift.lift_bnf_cmd ((((([], [(SOME Binding.empty, ("'a", NONE))]), "LQ.pq"), []), NONE),
        (Binding.empty, Binding.empty, Binding.empty)) (Named_Target.theory_init thy))),
  (*with the user's theorems -- pq's quotient theorem at n = 1 and its relation's reflexivity --
    lift_bnf reads the table only after its two goals (bnf_lift.ML mk_transfer_thms)*)
  ("O10 via", fn () =>
    let
      val lq1 =
        Goal.prove ctxt [] [] \<^prop>\<open>LQ (1 :: nat)\<close> (fn {context, ...} =>
          Locale.intro_locales_tac {strict = false, eager = true} context [] THEN
            ALLGOALS (asm_full_simp_tac context));
      val quot =
        #quot_thm (the (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>LQ.pq\<close>));
      val refl =
        Goal.prove ctxt [] []
          \<^prop>\<open>reflp (\<lambda>xs ys :: 'a list. length xs = length ys)\<close>
          (fn {context, ...} => simp_tac (context addsimps @{thms reflp_def}) 1);
    in
      refuses (only_in "LQ.pq" "LQ") (fn () =>
        BNF_Lift.lift_bnf
          ((((([], [(SOME Binding.empty, ("'a", NONE))]), \<^type_name>\<open>LQ.pq\<close>), NONE),
            SOME [quot OF [lq1], refl]), (Binding.empty, Binding.empty, Binding.empty))
          (replicate 2 (fn {context, ...} => Skip_Proof.cheat_tac context 1))
          (Named_Target.theory_init thy))
    end),
  ("O12 restore", fn () => (Test_Support.fails_prefix sanity
    (fn () => Lifting_Setup.lifting_restore {quot_thm = unpredicated, pcr_info = NONE}
      (Context.Proof ctxt)); true)),
  ("O12 lift_definition", fn () => raises_TERM
    (fn () =>
      lift_def ("h0", "HQ.hq", "0 :: nat") (with_unpredicated (Named_Target.theory_init thy)))),
  ("O13 lift_definition", fn () => raises_TERM
    (fn () => lift_def ("h1", "HQ.hq", "0 :: nat") (Named_Target.theory_init thy))),
  ("O13 includes", fn () =>
    (Test_Support.fails_prefix sanity (fn () => includes thy "HQ.hq.lifting"); true)),
  (*the check reads the first of the leading K premises, behind a top-level SORT_CONSTRAINT
    (ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.3b)*)
  ("F3 sort constraint first", fn () =>
    let
      val q = #quot_thm (the (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>LQ.qt\<close>));
      val q' = q |> Thm.implies_intr \<^cprop>\<open>SORT_CONSTRAINT('c::type)\<close> |> Setclass.put 1;
    in
      Setclass.count_of q' = 1 andalso
      refuses (only_in "LQ.qt" "LQ")
        (fn () => Lifting_Info.check_quotient ctxt {quot_thm = q', pcr_info = NONE})
    end)];
\<close>

end
