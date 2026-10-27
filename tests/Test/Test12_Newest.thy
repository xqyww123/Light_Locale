(* Plan section 7 test 12 (repair phase, step 1), "the newest fact that fails the variable
   condition is passed over" (batch-1 plan section 4.1): in the reopened block the newest fact
   LFt S would bind tS's ?S, which also occurs in the conclusion; the older schematic fact LFt ?x
   from interpretation I: LFt x for x discharges the premise. *)
theory Test12_Newest
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale LFt = fixes S :: "'a set" assumes triv: "S \<subseteq> UNIV"
lemma (in LFt) tS: "S = S" by (rule refl)

interpretation I: LFt x for x :: "'c set" by (rule LFt.intro) (rule subset_UNIV)

context LFt begin
ML \<open>
check_rows
 [("newest guard", fn () =>
    map Thm.prop_of (Light_Locale_Axiom_Facts.retrieve \<^context> \<^prop>\<open>LFt S\<close>)
    |> (fn ts => length ts = 2 andalso hd ts aconv \<^prop>\<open>LFt S\<close>)),
  ("tS", fn () => discharges \<^context> 1 (Global_Theory.get_thm \<^theory> "LFt.tS"))]
\<close>
end

end
