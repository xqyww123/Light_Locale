(* Sibling A (Heavy side): steps 3 and 4 -- J: HB x z for x z, then Q: K4 x for x, whose arrival at
   HB [?x, c] is filtered while no aconv-equal record of [?x, c] exists; afterwards there is no such
   record at all. *)
theory Test5_SibH_A
  imports Test5_SibH_T0
begin

interpretation J: HB x z for x z by unfold_locales simp_all
interpretation Q: K4 x for x by unfold_locales simp_all

ML \<open>
val xc = [Var (("x", 0), \<^typ>\<open>nat\<close>), \<^term>\<open>c\<close>];
val _ = \<^assert> (not (exists (fn (inst, _, _) => eq_list (op aconv) (inst, xc))
  (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" xc)));
val _ = \<^assert> (Test_Support.facts_under \<^theory> "Test5_SibH_A.Q." = ["Test5_SibH_A.Q.K4_axioms"]);
\<close>

end
