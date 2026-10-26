(* Plan section 7 test 7, plan lines 4919-4923: ".." on package rules.  After inductive ev (and od,
   with a single introduction rule, for the obtain shape) in LP's declaration block -- the
   parameter S does not occur in them, so the theory constants are LP.ev :: nat => bool and
   LP.od -- in a reopened block: show "LP.ev 0" .. fails (the theory copy LP ?S ==> LP.ev ?S 0
   leaves LP S), using LP_axioms .. succeeds; from LP_axioms h show "LP.ev (Suc (Suc n))" ..
   succeeds, from h alone fails; the elimination through LP.od.cases, whose derived rule has the
   major premise first: from h LP_axioms obtain ... .. succeeds, from h obtain ... .. fails.  The
   heavy twin's unchained rows and the light declaration block's unchained rows (the local
   ev.intros/od.cases) succeed. *)
theory Test7_Package_Rule
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

light_locale LP = fixes S :: nat assumes "S = S"
locale DP = fixes S :: nat assumes "S = S"

context LP begin
inductive ev :: "nat \<Rightarrow> bool" where ev0: "ev 0" | evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
inductive od :: "nat \<Rightarrow> bool" where odS: "od n \<Longrightarrow> od (Suc n)"
(*the declaration block: the local rules, unchained*)
lemma "ev 0" ..
lemma assumes h: "ev n" shows "ev (Suc (Suc n))" using h ..
lemma assumes h: "od (Suc m)" shows "od m"
proof -
  from h obtain m' where "Suc m = Suc m'" and "od m'" ..
  then show "od m" by simp
qed
end

context DP begin
inductive ev :: "nat \<Rightarrow> bool" where ev0: "ev 0" | evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
inductive od :: "nat \<Rightarrow> bool" where odS: "od n \<Longrightarrow> od (Suc n)"
lemma "ev 0" ..
lemma assumes h: "ev n" shows "ev (Suc (Suc n))" using h ..
lemma assumes h: "od (Suc m)" shows "od m"
proof -
  from h obtain m' where "Suc m = Suc m'" and "od m'" ..
  then show "od m" by simp
qed
end

context LP begin
(*the theory copies: chaining LP_axioms where the derived rule asks for it*)
lemma "LP.ev 0" using LP_axioms ..
lemma assumes h: "LP.ev n" shows "LP.ev (Suc (Suc n))" using LP_axioms h ..
lemma assumes h: "LP.od (Suc m)" shows "LP.od m"
proof -
  from h LP_axioms obtain m' where "Suc m = Suc m'" and "LP.od m'" ..
  then show "LP.od m" by simp
qed
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (not (by_method ctxt [] "standard" "LP.ev 0"));
val (h, ctxt') = assume_in ctxt [("n", \<^typ>\<open>nat\<close>)] "h" "LP.ev n";
val _ = \<^assert> (not (by_method ctxt' [h] "standard" "LP.ev (Suc (Suc n))"));
(*the elimination from h alone: the derived rule LP.od ?x ==> LP ?S ==> ... is not applied, so
  even the one-case goal that the chained elimination would leave is not reached*)
val (h', ctxt'') = assume_in ctxt [("m", \<^typ>\<open>nat\<close>)] "h'" "LP.od (Suc m)";
val _ = \<^assert> (by_method ctxt'' [h', @{thm LP_axioms}] "standard, simp" "LP.od m");
val _ = \<^assert> (not (by_method ctxt'' [h'] "standard, simp" "LP.od m"));
in end\<close>
end

end
