(* Plan section 7 test 6 (plan line 4659): the row-level "for" passes LF.* through the stock
   export -- lemmas fooPf [dest] = LF.fooP[of _ y] for y in a reopened context LF: K 1 (second
   version: the row-level for's Variable.export keeps K), and the derived dest rule's major
   premise is still LF ?S, since fooP has no own premise and own_major_prem falls back to the
   first premise. *)
theory Test6_Tag_For
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

context LF begin
lemma fooP: "Pc x y" by (rule Pc_ax)
end

context LF begin
lemmas fooPf [dest] = LF.fooP[of _ y] for y
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm LF.fooPf} = 1)\<close>
ML \<open>
val _ = \<^assert> (major_prem_is \<^context> "LF S" (#2 (claset_rule \<^context> Bires.dest_kind @{thm LF.fooPf})));
\<close>

end
