(* Plan section 7 test 7, plan lines 4867-4874.  named_theorems ns in the gate fixture's block:
   after reopening LF.ns is usable as a fact and as an attribute and the short name ns is not
   (failure only asserted); the heavy twin's short name works.  The three termination rows: after function (in LF) f ... by
   pat_completeness auto, termination (in LF) f reports "Not a function" (prefix only); an unnamed
   termination (in LF) whose proof is abandoned leaves only stable consequences -- LF.f.psimps
   defined, LF.f.simps not (which function it selected is not asserted); the control in one block,
   function g ... termination, gives LF.g.simps.  The TERM row: with the declaration-carrier
   abbreviation nab declared in HN before light_locale LN = HN, a syntax-only activation of HN
   (interpretation I: LN t) installs no intro! rule stated as TERM _ (Drule.dummy_thm) -- the
   controls: I.nab present, I.HN_axioms in the claset. *)
theory Test7_Function_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

context LF begin
named_theorems ns
end
context LF begin
ML \<open>
val _ = \<^assert> (has_fact \<^context> "LF.ns");
val _ = \<^assert> (not (has_fact \<^context> "ns"));
val _ = \<^assert> (can (Attrib.check_name \<^context>) ("LF.ns", Position.none));
val _ = \<^assert> (not (can (Attrib.check_name \<^context>) ("ns", Position.none)));
\<close>
end
context D begin
named_theorems nsd
end
context D begin
ML \<open>
val _ = \<^assert> (has_fact \<^context> "nsd");
val _ = \<^assert> (can (Attrib.check_name \<^context>) ("nsd", Position.none));
\<close>
end

context LF begin
function f :: "nat \<Rightarrow> nat" where "f 0 = 0" | "f (Suc n) = f n" by pat_completeness auto
end

ML \<open>
val lthy = Named_Target.init [] (Locale.check_global \<^theory> ("LF", Position.none)) \<^theory>;
val _ = fails_prefix "Not a function" (fn () => Function.termination_cmd (SOME "f") lthy);
\<close>

termination (in LF) oops

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (has_fact ctxt "LF.f.psimps" andalso not (has_fact ctxt "LF.f.simps"));
\<close>

context LF begin
function g :: "nat \<Rightarrow> nat" where "g 0 = 0" | "g (Suc n) = g n" by pat_completeness auto
termination by lexicographic_order
end

ML \<open>\<^assert> (has_fact (Proof_Context.init_global \<^theory>) "LF.g.simps")\<close>

(* the TERM row *)
locale HN = fixes a :: nat assumes "a = a"
abbreviation (in HN) nab where "nab \<equiv> a + 1"
light_locale LN = HN
consts t :: nat
interpretation I: LN t by unfold_locales simp

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (null (claset_entries ctxt Drule.dummy_thm));
val _ = \<^assert> (member (op =) (consts_named ctxt "nab") "Test7_Function_Block.I.nab");
val _ = \<^assert> (not (null (claset_entries ctxt @{thm I.HN_axioms})));
\<close>

end
