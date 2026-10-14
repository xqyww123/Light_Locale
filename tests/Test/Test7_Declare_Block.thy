(* Plan section 7 test 7: LF_axioms and the closure's predicate facts carry [simp, intro!] -- safe and clarify close the goals LF S and cring (UP S) in context LF (they do not simplify; only a safe intro rule closes them), clarsimp positively; the heavy control D_axioms with a hand-added [intro] is not used by safe.  Declarations of non-LF facts in the block (section 5.7): declare tsimp [simp del] in context LF removes the block copy only, with no message (no "Rewrite rule not in simpset:" entry); declare tintro [rule del] gives "Undeclared classical rule" and removes it from the block's claset only; declare LF_axioms [rule del] gives the same warning; in a reopened context LF simp uses tsimp again (the heavy twin D does not: its record replays the deletion); after declare (in LF) tsimp [simp del] a lemma (in LF) still proves by simp with tsimp (the heavy twin does not). *)
theory Test7_Declare_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_simp = proves (fn c => simp_tac c 1);
val by_safe = proves safe_tac;
val by_clarify = proves (fn c => clarify_tac c 1);
val by_clarsimp = proves (fn c => clarsimp_tac c 1);
val by_blast = proves (fn c => blast_tac c 1);
fun ws f = #2 (with_warnings f);
\<close>

context LF begin
ML_val \<open>
val _ = \<^assert> (by_safe \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_clarify \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_clarsimp \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_safe \<^context> \<^prop>\<open>cring (UP S)\<close>);
\<close>
end

context D begin
declare D_axioms [intro]
ML_val \<open>
val _ = \<^assert> (not (by_safe \<^context> \<^prop>\<open>D S\<close>));
val _ = \<^assert> (not (by_clarify \<^context> \<^prop>\<open>D S\<close>));
\<close>
end

definition k0 :: nat where "k0 = 0"
lemma tsimp [simp]: "k0 = 0" by (simp add: k0_def)
consts Pq :: "nat \<Rightarrow> bool"  c0 :: nat
axiomatization where tintro_ax: "Pq c0"
lemma tintro [intro]: "Pq c0" by (rule tintro_ax)

context LF begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "tsimp" "[simp del]")
  in \<^assert> (not (exists (String.isPrefix "Rewrite rule not in simpset:") w)); \<^assert> (null w); lthy' end\<close>
ML_val \<open>\<^assert> (not (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "tintro" "[rule del]")
  in \<^assert> (length w = 1 andalso String.isPrefix "Undeclared classical rule" (hd w)); lthy' end\<close>
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Pq c0\<close>))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF_axioms" "[rule del]")
  in \<^assert> (length w = 1 andalso String.isPrefix "Undeclared classical rule" (hd w)); lthy' end\<close>
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (by_simp ctxt \<^prop>\<open>k0 = 0\<close>);
val _ = \<^assert> (by_blast ctxt \<^prop>\<open>Pq c0\<close>);
\<close>

context LF begin
ML_val \<open>\<^assert> (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>)\<close>
end

context D begin
declare tsimp [simp del]
end
context D begin
ML_val \<open>\<^assert> (not (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>))\<close>
end

declare (in LF) tsimp [simp del]
lemma (in LF) lfsimp: "k0 = 0" by simp
declare (in D) tsimp [simp del]
ML \<open>
val _ = \<^assert> (not (can (fn () =>
  Named_Target.init [] (Locale.check_global \<^theory> ("D", Position.none)) \<^theory>
  |> (fn lthy => Goal.prove lthy [] [] \<^prop>\<open>k0 = 0\<close> (fn {context, ...} => simp_tac context 1))) ()));
\<close>

end
