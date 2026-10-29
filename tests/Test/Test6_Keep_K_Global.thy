(* Plan section 7 test 6, milestone 3's first item, second version (N10), with K counted as in
   ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.3: a theory-level block's registrations
   reach the theory's tables through the theory copy; an assumes layer pastes an ordinary premise
   in front, so the copy has K 0 and the registrations are stock's.  declare LF.foo [dest] in a
   theory-level assumes block registers Qc 0 ==> LF ?S ==> A ==> B ==> A & B with K 0, whose
   derived dest rule has major premise Qc 0; in a fixes-only block the theory copy is LF.foo with
   K 1, major premise A.  lemmas rc = LF.foo [cases pred: Rc] in the assumes block: K 0, the
   Induct entry keyed on Qc 0, default consumes 0 + 1.  The registrations are global, so this is
   its own leaf.
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

ML \<open>local
val key_shape = Logic.varify_global \<^prop>\<open>Qc (0::nat) \<Longrightarrow> LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>;
val (key, plain) =
  claset_rule_of Bires.dest_kind (claset_entries_by \<^context> (fn key => same_shape (Thm.prop_of key, key_shape)));
val _ = \<^assert> (Setclass.count_of key = 0);
val _ = \<^assert> (major_prem_is \<^context> "Qc (0::nat)" plain);
in end\<close>
ML \<open>
val _ = \<^assert> (Setclass.count_of @{thm rc} = 0 andalso Thm.nprems_of @{thm rc} = 4);
val _ = \<^assert> (Rule_Cases.get_consumes @{thm rc} = 1);
val _ = \<^assert> (is_some (induct_entry Induct.find_casesP \<^context> \<^prop>\<open>Qc (0::nat)\<close> @{thm rc}));
\<close>

context fixes w :: nat begin
declare LF.foo [dest]
end

ML \<open>local
val (key, plain) = claset_rule \<^context> Bires.dest_kind @{thm LF.foo};
val _ = \<^assert> (Setclass.count_of key = 1);
val _ = \<^assert> (major_prem_is \<^context> "A" plain);
in end\<close>

end
