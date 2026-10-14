(* The merge in the import order Test5_Merge_S2 Test5_Merge_S1: Locale.registrations_of returns exactly one entry
   for HB whose binding prefix is the full branch's qualifier Q; the heavy theorem is reachable under
   Q.; re-issuing the same interpretation is skipped without Duplicate fact declaration. *)
theory Test5_Merge_M21
  imports Test5_Merge_S2 Test5_Merge_S1
begin

ML \<open>
val regs = Locale.registrations_of (Context.Theory \<^theory>) (Locale.check_global \<^theory> ("HB", Position.none));
val _ = \<^assert> (map (fn (_, m) => Binding.long_name_of (Morphism.binding m (Binding.name "x"))) regs = ["Q.x"]);
val _ = \<^assert> (Test_Support.marks_of (Proof_Context.init_global \<^theory>) "HB" [\<^term>\<open>t\<close>] = [([\<^term>\<open>t\<close>], Locale.Full, [])]);
val _ = \<^assert> (Thm.prop_of @{thm Q.hb} aconv \<^prop>\<open>t = t\<close>);
\<close>

interpretation Q: HB t by unfold_locales simp

ML \<open>val _ = \<^assert> (null (Test_Support.facts_under \<^theory> "Test5_Merge_M21."))\<close>

end
