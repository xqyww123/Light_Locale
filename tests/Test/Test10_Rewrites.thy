(* Plan section 7 test 10 (sublocale from a light locale), with rewrites: inside context LF begin
   the abbreviation b.ba and b.B_axioms are rewritten (the instance x + 1 becomes Suc x) and no
   theorem of B is present; a reopened block agrees; after interpret ... rewrites ... in a proof the
   theorem b.bl agrees with the heavy twin's. *)
theory Test10_Rewrites
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale B = fixes u :: nat assumes bu: "u = u"
abbreviation (in B) ba where "ba \<equiv> u + 1"
lemma (in B) bl: "u + 0 = u" by simp

light_locale LF = fixes x :: nat assumes "x = x"
locale D = fixes x :: nat assumes "x = x"
sublocale LF \<subseteq> b: B "x + 1" rewrites "x + 1 = Suc x" by unfold_locales simp_all
sublocale D \<subseteq> b: B "x + 1" rewrites "x + 1 = Suc x" by unfold_locales simp_all

ML \<open>
fun check ctxt =
  let
    val _ = \<^assert> (rhs_of ctxt "local.b.ba" aconv \<^term>\<open>Suc x + 1\<close>);
    val _ = \<^assert> (Thm.prop_of (Proof_Context.get_thm ctxt "b.B_axioms") aconv \<^prop>\<open>B (Suc x)\<close>);
    val _ = \<^assert> (not (can (Proof_Context.get_thm ctxt) "b.bl"));
  in () end;
\<close>

context LF begin
ML_val \<open>check \<^context>\<close>
end
context LF begin
ML_val \<open>check \<^context>\<close>
lemma True
proof -
  interpret b: B "x + 1" rewrites "x + 1 = Suc x" by unfold_locales simp_all
  ML_val \<open>\<^assert> (Thm.prop_of @{thm b.bl} aconv \<^prop>\<open>Suc x + 0 = Suc x\<close>)\<close>
  show True ..
qed
end
context D begin
ML_val \<open>\<^assert> (Thm.prop_of @{thm b.bl} aconv \<^prop>\<open>Suc x + 0 = Suc x\<close>)\<close>
end

end
