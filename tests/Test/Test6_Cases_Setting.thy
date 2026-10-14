(* Plan section 7 test 6, the predicate-free Setting rows (plan lines 4536-4538, 4548-4551):
   lemma r [case_names a b] in light_locale Setting = fixes n :: nat has neither a consumes nor an
   exported_premises tag and is equal up to K (K 0) to the heavy twin's block r; lemmas rs [cases
   set: Aset] = Setting.r is equal up to K to the twin's row (numbered cases, consumes 1 -- the
   export generalises n and clears the tags) and find_casesP finds the stored rule by the set
   membership. *)
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
context Setth begin
lemmas rs [cases set: Aset] = r
ML \<open>val heavy_rs = @{thm rs};\<close>
end

light_locale Setting = fixes n :: nat
context Setting begin
lemma r [case_names a b]: "x \<in> Aset \<Longrightarrow> (x \<in> Aset \<Longrightarrow> W) \<Longrightarrow> (x \<notin> Aset \<Longrightarrow> W) \<Longrightarrow> W" by blast
end
ML \<open>
val tags = Thm.get_tags @{thm Setting.r};
val _ = \<^assert> (not (AList.defined (op =) tags "consumes") andalso not (has_K_tag @{thm Setting.r}));
val _ = \<^assert> (diff_K (@{thm Setting.r}, heavy_r) andalso Exported_Premises.count_of @{thm Setting.r} = 0);
\<close>
context Setting begin
lemmas rs [cases set: Aset] = Setting.r
end
ML \<open>
val _ = \<^assert> (diff_K (@{thm Setting.rs}, heavy_rs) andalso Exported_Premises.count_of @{thm Setting.rs} = 0);
val _ = \<^assert> (Rule_Cases.get @{thm Setting.rs} = ([(("1", []), []), (("2", []), [])], 1));
val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>x \<in> Aset\<close> @{thm Setting.rs};
val _ = \<^assert> (Thm.prop_of e aconv Thm.prop_of @{thm Setting.rs});
\<close>

end
