(* Plan section 7 test 6 (plan lines 4720-4721): [Pure.intro] and then [Pure.elim] on the same fact
   leave only the elim entry (stock's by-kind replacement in Context_Rules), read from the two nets
   of Context_Rules.netpair, in the block and (the light theory copy's registration) at theory
   level; the elim net holds the rule in its elim form (for the light theory copy the K-aware
   transposition Pc ?x ==> LF ?S ==> ..., for the heavy twin the rule itself).  The heavy twin's
   block as the control. *)
theory Test6_Del_PureIntroElim
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

ML \<open>
fun in_intros ctxt th = exists (fn (_, (_, r)) => Thm.eq_thm_prop (r, th)) (Net.entries (#1 (Context_Rules.netpair ctxt)));
fun in_elims ctxt th =
  exists (fn (_, (_, r)) => Thm.eq_thm_prop (r, Bires.kind_make_elim Bires.elim_kind th))
    (Net.entries (#2 (Context_Rules.netpair ctxt)));
\<close>

context D begin
lemma fooPIE: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end
context D begin
declare fooPIE [Pure.intro]
ML_val \<open>\<^assert> (in_intros \<^context> @{thm fooPIE} andalso not (in_elims \<^context> @{thm fooPIE}))\<close>
declare fooPIE [Pure.elim]
ML_val \<open>\<^assert> (not (in_intros \<^context> @{thm fooPIE}) andalso in_elims \<^context> @{thm fooPIE})\<close>
end

context LF begin
lemma fooPIE: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
declare LF.fooPIE [Pure.intro]
ML_val \<open>\<^assert> (in_intros \<^context> @{thm LF.fooPIE} andalso not (in_elims \<^context> @{thm LF.fooPIE})
  andalso in_intros (thy_ctxt \<^context>) @{thm LF.fooPIE})\<close>
declare LF.fooPIE [Pure.elim]
ML_val \<open>
val _ = \<^assert> (not (in_intros \<^context> @{thm LF.fooPIE}) andalso in_elims \<^context> @{thm LF.fooPIE});
val tctxt = thy_ctxt \<^context>;
val _ = \<^assert> (not (in_intros tctxt @{thm LF.fooPIE}) andalso in_elims tctxt @{thm LF.fooPIE});
\<close>
end

end
