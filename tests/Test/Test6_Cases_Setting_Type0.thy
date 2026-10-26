(* Plan section 7 test 6 (plan lines 4551-4553): the [consumes 0, cases type: TT] variant of the
   Setting row, its own leaf: Setting.rt is Setting.r' itself with case name a, consumes 0 and
   no K tag (second version). *)
theory Test6_Cases_Setting_Type0
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
typedecl TT

locale Setth = fixes n :: nat
context Setth begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
lemmas rt [consumes 0, cases type: TT] = r'
ML \<open>val _ = \<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>))\<close>
end

light_locale Setting = fixes n :: nat
context Setting begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
end
context Setting begin
lemmas rt [consumes 0, cases type: TT] = Setting.r'
end
ML \<open>
val _ = \<^assert> (Rule_Cases.get @{thm Setting.rt} = ([(("a", []), [])], 0));
val _ = \<^assert> (not (has_K_tag @{thm Setting.rt}) andalso Thm.eq_thm_prop (@{thm Setting.rt}, @{thm Setting.r'}));
\<close>
ML \<open>
val _ = \<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm Setting.rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>));
\<close>

end
