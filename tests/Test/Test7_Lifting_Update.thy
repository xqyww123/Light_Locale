(* Plan section 7 test 7 (milestone 3's first item, second version, N22): lifting_update inside
   the gate fixture's block re-declares the active transfer rules of a lifting bundle into its
   restore data -- the one patched HOL site of the redeclaration flag.  They are stored as they
   are: no K, no LF ?S in front; without the flag each would come back as LF ?S ==> rule with
   K 1.  int.lifting cannot serve as the fixture: Int.thy forgets it right after its
   lifting_update, so no transfer rule of int is active and the update would store nothing.
   Hence a fresh type with an active Lifting setup, whose restore data starts empty. *)
theory Test7_Lifting_Update
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

typedef tq = "UNIV :: nat set" by (rule UNIV_witness)
setup_lifting type_definition_tq
lift_definition zq :: tq is "0::nat" .

context LF begin
lifting_update tq.lifting
end

(* the restore data is keyed by the bundle's full name (lifting_setup.ML:237); the net holds the
   rules in the Transfer.Rel form of the transfer_raw net, so zq's rule is found by its constant *)
ML \<open>local
val bundle_name = Bundle.check \<^context> ("tq.lifting", Position.none);
val rules =
  Item_Net.content (#transfer_rules (the (Lifting_Info.lookup_restore_data \<^context> bundle_name)));
val _ = \<^assert> (exists (exists_Const (fn (c, _) => c = \<^const_name>\<open>zq\<close>) o Thm.prop_of) rules);
val _ = \<^assert> (forall (fn th => not (has_K_tag th) andalso null (light_prems \<^context> th)) rules);
in end\<close>

end
