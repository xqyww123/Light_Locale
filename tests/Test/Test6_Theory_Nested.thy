(* Plan section 7 test 6, the theory-level nested blocks of milestone 3's first item (plan lines
   4740-4749; section 11 (40)).  A theory-level context assumes ... begin block is a theory
   target: the copies a lemma leaves in the enclosing layers come from standard_notes (the outer
   copies), and the block reads its own layer's copy after each command.  t4 under two assumes
   layers: K = 1 + 1 between the two ends, the theory copy without K as before (milestone 3's
   narrow variant owns it); h3's row at theory level: the attribute's K on a lemma line survives
   the renumbering of the own layer's copy.  The usage convention (plan line 882): a lemma line's
   attribute is applied once more on the theory copy, so [exported_premises 1] on a lemma line
   in an assumes block gives the theory copy the absolute value 1 (fa); the lemmas spelling on
   the next line gives the block K 1 and the theory copy no K (fb; lemmas evaluates the static
   attribute before the notes); a fixes-only block is not affected (fc). *)
theory Test6_Theory_Nested
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"

context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
end

(* two theory-level assumes layers *)
context assumes c1: "Qc (1::nat)" begin
context assumes c2: "Qc (2::nat)" begin
lemmas t4 = LF.foo
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm t4} = 2 andalso Thm.nprems_of @{thm t4} = 4 andalso
  hd (Thm.prems_of @{thm t4}) aconv \<^prop>\<open>Qc (2::nat)\<close>)\<close>
end
ML_val \<open>\<^assert> (not (has_K_tag @{thm t4}) andalso Thm.nprems_of @{thm t4} = 5)\<close>

(* h3's row at theory level, read from the own layer's copy; the usage convention *)
context assumes c3: "Qc (3::nat)" begin
lemma h0: "Qc (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat)" for y by assumption
ML_val \<open>\<^assert> (Thm.maxidx_of @{thm h0[THEN conjunct1]} > 0)\<close>
lemma h3 [THEN conjunct1, exported_premises 1]: "Qc (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat)" for y by assumption
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm h3} = 1 andalso Thm.nprems_of @{thm h3} = 2)\<close>
lemma fa [exported_premises 1]: "Qc (3::nat) \<Longrightarrow> Qc (3::nat)" by assumption
lemmas fb [exported_premises 1] = fa
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fb} = 1 andalso Thm.nprems_of @{thm fb} = 1)\<close>
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fa} = 1 andalso Thm.nprems_of @{thm fa} = 2)\<close>
ML_val \<open>\<^assert> (not (has_K_tag @{thm fb}) andalso Thm.nprems_of @{thm fb} = 2)\<close>
context fixes v :: nat begin
lemma fc [exported_premises 1]: "Qc v \<Longrightarrow> Qc v" by assumption
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fc} = 1 andalso Thm.nprems_of @{thm fc} = 1)\<close>

end
