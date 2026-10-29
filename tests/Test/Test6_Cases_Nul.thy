(* Plan section 7 test 6, the element-free locale rows (plan lines 4539-4547): in light_locale Nul
   without elements, nfoo [case_names a b] and lemmas nh [consumes 1] = Nul.nfoo: Nul.nfoo carries
   no tag of ours (K 0) and the redeclaration is stored as the theorem itself, so Nul.nh and the
   local copy nh alike keep case names a b and consumes 1, with the same case info as Nul.nfoo,
   K 0, no setclass tag (second version: the local copy is the theorem itself too); the
   heavy twin's block nh lost case_names through Local_Defs.contract (consumes 1, numbered
   cases), so neither copy equals it. *)
theory Test6_Cases_Nul
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale Nulh
context Nulh begin
lemma nfoo [case_names a b]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemmas nh [consumes 1] = nfoo
ML \<open>val heavy_nh = @{thm nh};\<close>
end

light_locale Nul
context Nul begin
lemma nfoo [case_names a b]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemmas nh [consumes 1] = Nul.nfoo
ML \<open>val _ = \<^assert> (Thm.eq_thm_prop (@{thm nh}, @{thm Nul.nfoo}) andalso not (has_K_tag @{thm nh}))\<close>
ML \<open>val _ = \<^assert> (Rule_Cases.get @{thm nh} = ([(("a", []), []), (("b", []), [])], 1))\<close>
ML \<open>val _ = \<^assert> (not (Rule_Cases.get @{thm nh} = Rule_Cases.get heavy_nh))\<close>
end

ML \<open>
val _ = \<^assert> (Rule_Cases.get @{thm Nul.nh} = ([(("a", []), []), (("b", []), [])], 1));
val _ = \<^assert> (#1 (Rule_Cases.get @{thm Nul.nh}) = #1 (Rule_Cases.get @{thm Nul.nfoo}));
val _ = \<^assert> (Setclass.count_of @{thm Nul.nh} = 0 andalso not (has_K_tag @{thm Nul.nh}));
val _ = \<^assert> (not (Thm.eq_thm_prop (@{thm Nul.nh}, heavy_nh) andalso Rule_Cases.get @{thm Nul.nh} = Rule_Cases.get heavy_nh));
\<close>

end
