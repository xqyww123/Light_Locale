(* Plan section 7 test 3 (opening), the rows on a block lemma foo [simp] and a block inductive ipx
   in the gate fixture.  LF.foo is a global simp rule, so these rows have their own leaf. *)
theory Test3_Foo
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

axiomatization k :: "('a, 'b) ring_scheme \<Rightarrow> nat" and k2 :: "('a, 'b) ring_scheme \<Rightarrow> nat"
  where kS: "k R = 0" and k2S: "k2 R = 0"

ML \<open>
fun has_fact ctxt name = can (Proof_Context.get_fact ctxt) (Facts.named name);
\<close>

context D begin
lemma foo: "k S = 0" by (rule kS)
ML_val \<open>\<^assert> (Thm.prop_of @{thm foo} aconv @{prop "k S = 0"})\<close>
end

(* in the block: foo is the unconditional local copy, Thm.eq_thm_prop with the heavy block's foo;
   a goal that needs it is closed by simp *)
context LF begin
lemma foo [simp]: "k S = 0" by (rule kS)
ML_val \<open>\<^assert> (Thm.prop_of @{thm foo} aconv @{prop "k S = 0"})\<close>
lemma "k S + 1 = 1" by simp
(* after a lemma (in LF) in the same block, its own short name and the earlier copy foo are gone *)
lemma (in LF) foo' [simp]: "k2 S = 0" by (rule k2S)
ML_val \<open>\<^assert> (not (has_fact \<^context> "foo'") andalso not (has_fact \<^context> "foo"))\<close>
end

(* reopened: foo is not defined; simp closes the goal with LF.foo, its condition LF S discharged
   through LF_axioms [simp] *)
context LF begin
ML_val \<open>\<^assert> (not (has_fact \<^context> "foo"))\<close>
lemma "k S + 1 = 1" by simp
ML_val \<open>\<^assert> (Thm.prop_of @{thm LF.foo[OF LF_axioms]} aconv @{prop "k S = 0"})\<close>
end

ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.foo} = 1);
(*negative control: without the predicate fact the same goal is not closed by simp*)
val ctxt = \<^context>;
val _ = \<^assert> (not (can (fn () =>
  Goal.prove ctxt ["T"] [] @{prop "k (T :: ('a, 'b) ring_scheme) + 1 = 1"}
    (fn {context, ...} => simp_tac context 1)) ()));
\<close>

(* a block inductive: after a lemma (in LF) in the same block, "using h proof cases" no longer finds
   ipx.cases (stored as LF ?S ==> ..., one exported premise) and falls back to case_split, whose
   cases do not include ip0; chaining LF_axioms first finds it.  The heavy twin finds it unchained. *)
context LF begin
inductive ipx :: "nat \<Rightarrow> bool" where ip0: "ipx 0"
lemma (in LF) t: True ..
lemma assumes h: "ipx x" shows "x = 0"
  using h proof cases
  ML_val \<open>\<^assert> (map #1 (Proof_Context.dest_cases NONE \<^context>) = ["True", "False"])\<close>
  oops
lemma assumes h: "ipx x" shows "x = 0"
  using LF_axioms h proof cases
  ML_val \<open>\<^assert> (map #1 (Proof_Context.dest_cases NONE \<^context>) = ["ip0"])\<close>
  case ip0 then show ?thesis by simp
qed
end

context D begin
inductive ipx :: "nat \<Rightarrow> bool" where ip0: "ipx 0"
lemma (in D) t: True ..
lemma assumes h: "ipx x" shows "x = 0"
  using h proof cases
  case ip0 then show ?thesis by simp
qed
end

end
