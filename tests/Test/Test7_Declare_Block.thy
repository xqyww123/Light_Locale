(* Plan section 7 test 7: LF_axioms and the closure's predicate facts carry [simp, intro!] --
   safe and clarify close the goals LF S and cring (UP S) in context LF (they do not simplify;
   only a safe intro rule closes them), clarsimp positively; the heavy control D_axioms with a
   hand-added [intro] is not used by safe.  Declarations of non-LF facts in the block (section
   5.7; milestone 3's first item, second version): a redeclaration of a fact unrelated to the
   block is stored as the theorem itself, so declare tsimp [simp del] in context LF removes tsimp
   from the global simpset for good, with no message; declare tintro [rule del] likewise removes
   tintro for good, with no warning (the theory level finds tintro itself); declare LF_axioms
   [rule del] gives "Undeclared classical rule".  Each deletion has its positive control before
   it.  The (in ...) pairs on tsimp5: after declare (in D) tsimp5 [simp del] D's target does not
   prove k5 = 0 by simp; after declare (in LF) tsimp5 [simp del] neither LF's target nor the
   theory does. *)
theory Test7_Declare_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
val by_safe = proves safe_tac;
val by_clarify = proves (fn c => clarify_tac c 1);
val by_clarsimp = proves (fn c => clarsimp_tac c 1);
\<close>

context LF begin
ML \<open>
val _ = \<^assert> (by_safe \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_clarify \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_clarsimp \<^context> \<^prop>\<open>LF S\<close>);
val _ = \<^assert> (by_safe \<^context> \<^prop>\<open>cring (UP S)\<close>);
\<close>
end

context D begin
declare D_axioms [intro]
ML \<open>
val _ = \<^assert> (not (by_safe \<^context> \<^prop>\<open>D S\<close>));
val _ = \<^assert> (not (by_clarify \<^context> \<^prop>\<open>D S\<close>));
\<close>
end

definition k0 :: nat where "k0 = 0"
lemma tsimp [simp]: "k0 = 0" by (simp add: k0_def)
consts Pq :: "nat \<Rightarrow> bool"  c0 :: nat
axiomatization where tintro_ax: "Pq c0"
lemma tintro [intro]: "Pq c0" by (rule tintro_ax)

(* a positive control first: the block's simp proves k0 = 0 by tsimp *)
context LF begin
ML \<open>val _ = \<^assert> (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>)\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "tsimp" "[simp del]")
  in \<^assert> (not (exists (String.isPrefix "Rewrite rule not in simpset:") w)); \<^assert> (null w); lthy' end\<close>
ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>))\<close>
(* tintro: the positive control; the deletion's warnings, read on a throw-away context (the theory
   level finds tintro itself and deletes it without a word); then the deletion itself *)
ML \<open>val _ = \<^assert> (by_blast \<^context> \<^prop>\<open>Pq c0\<close>)\<close>
ML \<open>val _ = \<^assert> (null (#2 (with_warnings (fn () => declare_in \<^context> "tintro" "[rule del]"))))\<close>
declare tintro [rule del]
ML \<open>val _ = \<^assert> (not (by_blast \<^context> \<^prop>\<open>Pq c0\<close>))\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF_axioms" "[rule del]")
  in \<^assert> (length w = 1 andalso String.isPrefix "Undeclared classical rule" (hd w)); lthy' end\<close>
end

(* the redeclarations are the theorems themselves, so the deletions are global and permanent *)
ML \<open>val _ = \<^assert> (not (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k0 = 0\<close>))\<close>
ML \<open>val _ = \<^assert> (not (by_blast (Proof_Context.init_global \<^theory>) \<^prop>\<open>Pq c0\<close>))\<close>

context LF begin
ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>k0 = 0\<close>))\<close>
end

(* the (in ...) pairs on their own fact tsimp5: first the heavy pair (the positive control, the
   deletion, the negative), then the light pair *)
definition k5 :: nat where "k5 = 0"
lemma tsimp5 [simp]: "k5 = 0" by (simp add: k5_def)
ML \<open>local
val lthy = Named_Target.init [] (Locale.check_global \<^theory> ("D", Position.none)) \<^theory>;
val _ = \<^assert> (by_simp lthy \<^prop>\<open>k5 = 0\<close>);
in end\<close>
declare (in D) tsimp5 [simp del]
ML \<open>local
val lthy = Named_Target.init [] (Locale.check_global \<^theory> ("D", Position.none)) \<^theory>;
val _ = \<^assert> (not (by_simp lthy \<^prop>\<open>k5 = 0\<close>));
in end\<close>
(* the light pair: after declare (in LF) the deletion reaches the global simpset *)
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k5 = 0\<close>)\<close>
ML \<open>val _ = \<^assert> (by_simp (Named_Target.init [] (Locale.check_global \<^theory> ("LF", Position.none)) \<^theory>) \<^prop>\<open>k5 = 0\<close>)\<close>
declare (in LF) tsimp5 [simp del]
ML \<open>val _ = \<^assert> (not (by_simp (Named_Target.init [] (Locale.check_global \<^theory> ("LF", Position.none)) \<^theory>) \<^prop>\<open>k5 = 0\<close>))\<close>
ML \<open>val _ = \<^assert> (not (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>k5 = 0\<close>))\<close>

end
