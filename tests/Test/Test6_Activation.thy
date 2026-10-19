(* Plan section 7 test 6, the activation site of milestone 3's first item (section 11 (40)) under
   an interpretation that changes the premises themselves: Element.transform_ctxt puts K back as
   K + d, d the premises the morphism puts in front (here 0), with a range check as the door.
   K2.g: the rewrites mixin instantiates inside the first (the exported) premise, so a door that
   asks the leading K premises to be literally unchanged would drop K -- the regression pin of
   the door.  K6.h: a prop-typed parameter instantiated with an implication makes the
   normalisation split a premise off the conclusion at the end, so the premise count changes
   while the leading premise stays exported: K 1. *)
theory Test6_Activation
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pa :: "nat \<Rightarrow> bool"  Qa :: "nat \<Rightarrow> bool"  Ra :: bool  Sa :: "nat \<Rightarrow> prop"
axiomatization where Pa0: "Pa 0" and QaRa: "Qa 0 = Ra"

locale L5 = fixes x :: nat assumes a: "Pa x"
begin
lemma g [exported_premises 1]: "Pa x \<Longrightarrow> Qa x \<Longrightarrow> Qa x" by assumption
end
interpretation K2: L5 0 rewrites "Qa 0 = Ra" by (simp_all add: L5_def Pa0 QaRa)
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm K2.g} = 1 andalso Thm.nprems_of @{thm K2.g} = 2)\<close>

locale L6 = fixes T :: "prop" and x :: nat assumes a: "Pa x"
begin
lemma h [exported_premises 1]: "Pa x \<Longrightarrow> PROP T \<Longrightarrow> PROP T" by assumption
end
interpretation K6: L6 "PROP Sa 0 \<Longrightarrow> PROP Sa 1" 0 by (simp add: L6_def Pa0)
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm K6.h} = 1 andalso Thm.nprems_of @{thm K6.h} = 3)\<close>

end
