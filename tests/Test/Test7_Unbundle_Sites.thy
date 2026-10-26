(* Plan section 7 test 7, milestone 3's first item, second version (N21): applying a bundle in a
   light block is a redeclaration.  The one set point is the local-theory branch of bundle.ML's
   apply_bundle, which every entry goes through; the three entries -- the command unbundle, the
   ML entry Bundle.unbundle, and open_bundle defined inside the block -- are each pinned by a row
   of their own, so an entry that stops going through apply_bundle shows up here.  Each row has its own
   rule, which is not a simp rule before: the negative control first, then the block, then
   theory-level simp proves the goal without a condition, because the redeclared rule is stored as
   itself.  The simpset changes for good, so this is its own leaf. *)
theory Test7_Unbundle_Sites
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts sq :: "nat \<Rightarrow> nat"  mq :: "nat \<Rightarrow> nat"  oq :: "nat \<Rightarrow> nat"
axiomatization where s_rule: "sq 0 = 0" and m_rule: "mq 0 = 0" and o_rule: "oq 0 = 0"

ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>sq 0 = 0\<close>))\<close>
ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>mq 0 = 0\<close>))\<close>
ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>oq 0 = 0\<close>))\<close>

(* (1) the command *)
bundle bs = s_rule [simp]
context LF begin
unbundle bs
end
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>sq 0 = 0\<close>)\<close>

(* (2) the ML entry, on a bundle of its own *)
bundle bm = m_rule [simp]
context LF begin
local_setup \<open>fn lthy => Bundle.unbundle [(true, Bundle.check lthy ("bm", Position.none))] lthy\<close>
end
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>mq 0 = 0\<close>)\<close>

(* (3) open_bundle defined inside the block *)
context LF begin
open_bundle bo = o_rule [simp]
end
ML \<open>val _ = \<^assert> (by_simp (Proof_Context.init_global \<^theory>) \<^prop>\<open>oq 0 = 0\<close>)\<close>

end
