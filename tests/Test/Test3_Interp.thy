(* Plan section 7 test 3 (opening): after interpretation I: LF t, the predicate fact I.LF_axioms
   exists, the block lemma and the heavy theorems do not; the heavy twin's interpretation has them.
   The facts LF reaches through its edge to UP_cring (which eliminated P == UP S) carry no definition
   hyp, in the block and after the interpretation (plan section 11, implementation-period change
   (11)). *)
theory Test3_Interp
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

axiomatization t :: "nat ring" where t: "cring t"

context LF begin
lemma foo: "S = S" ..
lemma u: "cring (UP S)" by (rule P.cring_axioms)
ML \<open>val _ = \<^assert> (null (Test_Support.extra_hyps \<^context> "P.cring_axioms"))\<close>
end

context D begin
lemma foo: "S = S" ..
end

interpretation I: LF t by (simp add: LF_def UP_cring_def t)

interpretation J: D "UP t" t by (rule D.intro) (simp add: UP_cring_def t)

ML \<open>local
val has_fact = Test_Support.has_fact \<^context>;
val _ = \<^assert> (has_fact "I.LF_axioms");
val _ = \<^assert> (not (exists has_fact ["I.foo", "I.R.m_comm", "I.R.is_cring"]));
val _ = \<^assert> (forall has_fact ["J.foo", "J.R.m_comm", "J.R.is_cring"]);
val _ = \<^assert> (null (Test_Support.extra_hyps \<^context> "I.P.cring_axioms"));
in end\<close>

end
