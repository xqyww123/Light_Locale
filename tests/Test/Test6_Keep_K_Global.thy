(* Plan section 7 test 6, milestone 3's first item, second version (N10): a theory-level block's
   registrations reach the theory's tables through the theory copy, which keeps K plus the
   premises the export puts in front.  declare LF.foo [dest] in a theory-level assumes block
   registers Qc 0 ==> LF ?S ==> A ==> B ==> A & B with K 2, whose derived dest rule has major
   premise A; in a fixes-only block the theory copy is LF.foo with K 1, major premise A again.
   lemmas rc = LF.foo [cases pred: Rc] in the assumes block: K 2, the Induct entry keyed on A,
   default consumes K + 1 = 3.  The registrations are global, so this is its own leaf.
   declare LF.foo [dest] is a mechanism fixture (it only shows which premise Classical takes as
   major), not a user scenario. *)
theory Test6_Keep_K_Global
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Qc :: 'a  Rc :: 'a

context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
end

context assumes hq: "Qc (0::nat)" begin
declare LF.foo [dest]
lemmas rc = LF.foo [cases pred: Rc]
end

ML_val \<open>
val key_shape = Logic.varify_global \<^prop>\<open>Qc (0::nat) \<Longrightarrow> LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>;
val (key, plain) =
  claset_rule_of Bires.dest_kind (claset_entries_by \<^context> (fn key => same_shape (Thm.prop_of key, key_shape)));
val _ = \<^assert> (Exported_Premises.count_of key = 2);
val _ = \<^assert> (major_prem_is \<^context> "A" plain);
\<close>
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm rc} = 2 andalso Thm.nprems_of @{thm rc} = 4);
val _ = \<^assert> (Rule_Cases.get_consumes @{thm rc} = 3);
val _ = \<^assert> (is_some (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>A\<close> @{thm rc}));
\<close>

context fixes w :: nat begin
declare LF.foo [dest]
end

ML_val \<open>
val (key, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.foo};
val _ = \<^assert> (Exported_Premises.count_of key = 1);
val _ = \<^assert> (major_prem_is \<^context> "A" plain);
\<close>

end
