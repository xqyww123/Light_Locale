(* Plan section 7 test 6 (plan line 4659): the row-level "for" passes LF.* through the stock
   export -- lemmas fooPf [dest] = LF.fooP[of _ y] for y in a reopened context LF: K 0 and the
   derived dest rule's major premise is LF ?S (the tag is cleared by the row-level for, LF ?S
   becomes the rule's own premise). *)
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
ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooPf} = 0);
val _ = \<^assert> (exists (fn (_, plain, _) => Light_Locale_Axiom_Facts.is_light_prop \<^context> (Thm.major_prem_of plain))
  (claset_entries \<^context> @{thm LF.fooPf}));
\<close>

end
