(* Plan section 7 test 5 (external use and propagation): sublocale propagation into a syntax-only registration: after light_locale LF = B and interpretation I: LF t, a downstream sublocale B <= C t' and a subclass install no theorem under I. (only the _axioms copies). *)
theory Test5_Propagation_Sublocale
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale B = fixes b :: nat assumes bb: "b = b"
locale C = fixes v :: nat assumes "v = v"
lemma (in C) cl: "v + 0 = v" by simp
consts t :: nat
light_locale LF = B
interpretation I: LF t by unfold_locales simp
sublocale B \<subseteq> C "b + 1" by unfold_locales simp

ML \<open>
val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Sublocale.I." =
  ["Test5_Propagation_Sublocale.I.B_axioms", "Test5_Propagation_Sublocale.I.C_axioms", "Test5_Propagation_Sublocale.I.LF_axioms"]);
\<close>

class cb = fixes cx :: 'a assumes cbax: "cx = cx"
class cc = assumes ccax: "\<forall>x::'a. x = x"
lemma (in cc) ccl: "\<forall>x::'a. x = x" by (rule ccax)
light_locale LFc = cb
interpretation Ic: LFc "0::nat" by unfold_locales simp

ML \<open>val ic = facts_under \<^theory> "Test5_Propagation_Sublocale.Ic."
val _ = \<^assert> (ic = ["Test5_Propagation_Sublocale.Ic.LFc_axioms", "Test5_Propagation_Sublocale.Ic.cb_axioms"])\<close>

subclass (in cb) cc by unfold_locales simp

ML \<open>val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Sublocale.Ic." = ic)\<close>

end
