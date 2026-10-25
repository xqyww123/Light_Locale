(* Plan ai-artifacts/LIGHT_LOCALE_TAT_INTERFACE_PLAN.md section 5 row E: a Lifting setup made in a
   block with an axiom is stored at theory level with the locale's predicate as the one premise of
   its quotient theorem, K = 1, as the two readers TAT calls return it: Lifting_Info.lookup_quotients
   by the type's name (TAT's LiftDefinition) and Lifting_Info.lookup_restore_data by the pointer the
   setup's bundle holds (TAT's LiftingContext).  At theory level the predicate is no fact, so this
   holds before and after the repair phase's second step, and it is the fact TAT's refusal
   (Exported_Premises.count_of > 0) relies on.  In the block of a light locale that imports LQ the
   predicate is a fact: that is where the second step is to discharge the premise in those readers,
   so the last row, which asserts K = 1 there today, is the one that step changes. *)
theory Test8_Lifting_Premise
  imports Test_Support
begin

(* the relation may not mention the parameter (quotient_type: "illegal variable(s) in the
   relation"); the premise comes from the block's assumption all the same *)
light_locale LQ = fixes n :: nat assumes pos: "0 < n"
begin
quotient_type qt = nat / "\<lambda>x y. x mod 2 = y mod 2"
  by (auto intro!: equivpI reflpI sympI transpI)
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
(*the quotient theorem of qt as the two readers return it: K, the light premises, all premises*)
fun premise_counts ctxt =
  let
    fun counts th =
      (Exported_Premises.count_of th, length (Test_Support.light_prems ctxt th),
        length (Thm.prems_of th));
    val by_type =
      #quot_thm (the (Lifting_Info.lookup_quotients ctxt \<^type_name>\<open>LQ.qt\<close>));
    val by_pointer =
      #quot_thm (#quotient (the (Lifting_Info.lookup_restore_data ctxt (restore_key ctxt "LQ.qt.lifting"))));
  in (counts by_type, counts by_pointer) end;
\<close>

ML_val \<open>\<^assert> (premise_counts \<^context> = ((1, 1, 1), (1, 1, 1)))\<close>

light_locale LQ_user = LQ
begin
(* K = 1 in the block today; the repair phase's second step discharges the premise here *)
ML_val \<open>\<^assert> (premise_counts \<^context> = ((1, 1, 1), (1, 1, 1)))\<close>
end

end
