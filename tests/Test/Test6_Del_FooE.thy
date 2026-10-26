(* Plan section 7 test 6 (plan lines 4715-4716, 4721): attribute order does not matter -- lemma
   fooE [elim, consumes 1, case_names Hyp] in the declaration block, end, reopen; what print_claset
   shows is read through the claset's declaration keys: LF.fooE's entry is there, in the block's
   and the theory's claset, with its first premise light; declare LF.fooE [rule del] succeeds
   without "Undeclared classical rule" and neither claset has an entry with its proposition. *)
theory Test6_Del_FooE
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooE [elim, consumes 1, case_names Hyp]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
(* the print_claset row: the declaration keys *)
ML \<open>local
val (key, _) = claset_rule \<^context> Bires.elim_kind @{thm LF.fooE};
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of key)));
val _ = claset_rule (thy_ctxt \<^context>) Bires.elim_kind @{thm LF.fooE};
in end\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.fooE" "[rule del]")
  in \<^assert> (not (exists (String.isPrefix "Undeclared classical rule") w)); lthy' end\<close>
ML \<open>val _ = \<^assert> (null (claset_entries \<^context> @{thm LF.fooE}))\<close>
end

ML \<open>val _ = \<^assert> (null (claset_entries \<^context> @{thm LF.fooE}));\<close>

end
