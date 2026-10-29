(* Plan section 7 test 6, the predicate-free Setting rows (plan lines 4536-4538, 4548-4551):
   lemma r [case_names a b] in light_locale Setting = fixes n :: nat has neither a consumes nor an
   setclass tag and is equal up to K (K 0) to the heavy twin's block r; lemmas rs [cases
   set: Aset] = Setting.r is stored as Setting.r itself (second version: a redeclaration whose
   export changes nothing keeps the theorem, case names a b included), the mixed attribute cases
   set applied once more on the stored copy gives it consumes 1 (default_consumes), no K tag;
   find_casesP finds the stored rule by the set membership. *)
theory Test6_Cases_Setting
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
consts Aset :: "nat set"

locale Setth = fixes n :: nat
context Setth begin
lemma r [case_names a b]: "x \<in> Aset \<Longrightarrow> (x \<in> Aset \<Longrightarrow> W) \<Longrightarrow> (x \<notin> Aset \<Longrightarrow> W) \<Longrightarrow> W" by blast
ML \<open>val heavy_r = @{thm r};\<close>
end

light_locale Setting = fixes n :: nat
context Setting begin
lemma r [case_names a b]: "x \<in> Aset \<Longrightarrow> (x \<in> Aset \<Longrightarrow> W) \<Longrightarrow> (x \<notin> Aset \<Longrightarrow> W) \<Longrightarrow> W" by blast
end
ML \<open>
val tags = Thm.get_tags @{thm Setting.r};
val _ = \<^assert> (not (AList.defined (op =) tags "consumes") andalso not (has_K_tag @{thm Setting.r}));
val _ = \<^assert> (diff_K 0 (@{thm Setting.r}, heavy_r));
\<close>
context Setting begin
lemmas rs [cases set: Aset] = Setting.r
end
ML \<open>
val _ = \<^assert> (Rule_Cases.get @{thm Setting.rs} = ([(("a", []), []), (("b", []), [])], 1));
val _ = \<^assert> (not (has_K_tag @{thm Setting.rs}) andalso Thm.eq_thm_prop (@{thm Setting.rs}, @{thm Setting.r}));
\<close>
ML \<open>
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>x \<in> Aset\<close> @{thm Setting.rs};
val _ = \<^assert> (Thm.prop_of e aconv Thm.prop_of @{thm Setting.rs});
\<close>

end
