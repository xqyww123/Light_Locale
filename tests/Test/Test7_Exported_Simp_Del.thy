(* Plan section 7 test 7: a theory fact re-declared without hyps inside the block is stored as itself, so its deletion is global (section 5.7, the rule at plan line 3300): st2 (first premise the light predicate) is in the theory simpset before, and after context LFs2 begin declare st2 [simp del] end it is gone, with no warning. *)
theory Test7_Exported_Simp_Del
  imports Test_Support
begin

ML \<open>open Test_Support\<close>


light_locale LFs2 = fixes S :: "'a set" assumes "finite S"
consts Sub2 :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
axiomatization where st2_ax: "LFs2 S \<Longrightarrow> Sub2 S S = True"
lemma st2 [simp]: "LFs2 S \<Longrightarrow> Sub2 S S = True" by (rule st2_ax)

ML \<open>
fun has_st2 ctxt = exists (fn ((n, _), _) => String.isSuffix "st2" n) (Raw_Simplifier.dest_simps (simpset_of ctxt));
val _ = \<^assert> (has_st2 (Proof_Context.init_global \<^theory>));
\<close>

context LFs2 begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "st2" "[simp del]")
  in \<^assert> (null w); lthy' end\<close>
end

ML \<open>val _ = \<^assert> (not (has_st2 (Proof_Context.init_global \<^theory>)))\<close>

end
