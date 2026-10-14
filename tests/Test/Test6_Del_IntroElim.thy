(* Plan section 7 test 6 (plan line 4720): the same fact declared [intro] and [elim] in the
   reopened block -- both kinds in the block's and the theory's claset -- is removed entirely by
   one [rule del], from both. *)
theory Test6_Del_IntroElim
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooIE: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
declare LF.fooIE [intro]
declare LF.fooIE [elim]
ML_val \<open>
fun both_kinds ctxt =
  let val kinds = map #3 (claset_entries ctxt @{thm LF.fooIE})
  in exists Bires.kind_is_elim kinds andalso exists (not o Bires.kind_is_elim) kinds end;
val _ = \<^assert> (forall both_kinds [\<^context>, thy_ctxt \<^context>]);
\<close>
declare LF.fooIE [rule del]
ML_val \<open>\<^assert> (null (claset_entries \<^context> @{thm LF.fooIE}))\<close>
end

ML \<open>val _ = \<^assert> (null (claset_entries \<^context> @{thm LF.fooIE}));\<close>

end
