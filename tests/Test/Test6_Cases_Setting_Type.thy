(* Plan section 7 test 6 (plan lines 4551-4553): lemmas rt [cases type: TT] = Setting.r' in the
   predicate-free Setting is equal up to K (K 0) to the heavy twin's row and find_casesT TT has an
   entry Thm.equiv_thm to the stored rule. *)
theory Test6_Cases_Setting_Type
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
typedecl TT

locale Setth = fixes n :: nat
context Setth begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
lemmas rt [cases type: TT] = r'
ML \<open>val heavy_rt = @{thm rt};\<close>
ML_val \<open>\<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>))\<close>
end

light_locale Setting = fixes n :: nat
context Setting begin
lemma r' [case_names a]: "(x = (x::TT) \<Longrightarrow> W) \<Longrightarrow> W" by simp
end
context Setting begin
lemmas rt [cases type: TT] = Setting.r'
end
ML \<open>
val _ = \<^assert> (diff_K 0 (@{thm Setting.rt}, heavy_rt));
val _ = \<^assert> (exists (fn r => Thm.equiv_thm \<^theory> (r, @{thm Setting.rt})) (Induct.find_casesT \<^context> \<^typ>\<open>TT\<close>));
\<close>

end
