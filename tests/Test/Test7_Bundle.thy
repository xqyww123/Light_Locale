(* Plan section 7 test 7, row (f) of the export-morphism group (plan line 4854): the bundle leaf.
   A theory fact gq0 without [simp] (simp does not prove gq 0 = 1: the control); inside the gate
   fixture's block, bundle bgq = gq0 [simp]; after the block the bundle reads back as exactly one
   entry whose theorem is gq0 itself (a closed theory fact: count_of 0) with its attribute source;
   unbundle LF.bgq at theory level then makes simp prove gq 0 = 1.  The theory-level unbundle
   changes the simpset for good, so this is its own leaf (section 7 preface); no interpretation of
   LF here. *)
theory Test7_Bundle
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

consts gq :: "nat \<Rightarrow> nat"
axiomatization where gq0: "gq 0 = 1"

ML \<open>val _ = \<^assert> (not (by_simp \<^context> \<^prop>\<open>gq 0 = 1\<close>))\<close>

context LF begin
bundle bgq = gq0 [simp]
end

ML \<open>val ctxt = Proof_Context.init_global \<^theory>\<close>
ML \<open>
val _ = \<^assert>
  (case bundle_of ctxt "LF.bgq" of
    [([th], srcs)] => Thm.eq_thm_prop (th, @{thm gq0}) andalso Exported_Premises.count_of th = 0 andalso not (null srcs)
  | _ => false);
val _ = \<^assert> (not (by_simp ctxt \<^prop>\<open>gq 0 = 1\<close>));
\<close>

unbundle LF.bgq

lemma "gq 0 = 1" by simp

end
