(* Plan section 7 test 6 (plan lines 4551-4553): lemmas rt [cases type: TT] = Setting.r' in the
   predicate-free Setting is stored as Setting.r' itself (second version: a redeclaration whose
   export changes nothing keeps the theorem, case name a included), cases type's default
   consumes 0 and no K tag, and find_casesT TT has an entry Thm.equiv_thm to the stored rule. *)
theory Test6_Cases_Setting_Type
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
typedecl TT

locale Setth = fixes n :: nat
context Setth begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
lemmas rt [cases type: TT] = r'
ML_val \<open>\<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>))\<close>
end

light_locale Setting = fixes n :: nat
context Setting begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
end
context Setting begin
lemmas rt [cases type: TT] = Setting.r'
end
ML_val \<open>
val _ = \<^assert> (Rule_Cases.get @{thm Setting.rt} = ([(("a", []), [])], 0));
val _ = \<^assert> (not (has_K_tag @{thm Setting.rt}) andalso Thm.eq_thm_prop (@{thm Setting.rt}, @{thm Setting.r'}));
\<close>
ML \<open>
val _ = \<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm Setting.rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>));
\<close>

end
