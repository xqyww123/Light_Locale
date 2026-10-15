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

(* the subclass half: cc shares the parameter cx with cb through c0, so that the cc instance of the
   subclass edge has a key ([cx]) that is not registered Full in advance (a parameter-free class
   is registered Full by the class command itself, and the edge would be pruned before any level) *)
class c0 = fixes cx :: 'a
class cb = c0 + assumes cbax: "cx = cx"
class cc = c0 + assumes ccax: "cx = cx"
lemma (in cc) ccl: "cx = cx" by (rule ccax)
light_locale LFc = cb
interpretation Ic: LFc "0::nat" by unfold_locales simp

ML \<open>val ic = facts_under \<^theory> "Test5_Propagation_Sublocale.Ic."
val _ = \<^assert> (ic = ["Test5_Propagation_Sublocale.Ic.LFc_axioms", "Test5_Propagation_Sublocale.Ic.cb_axioms"])\<close>

subclass (in cb) cc by unfold_locales simp

ML \<open>val _ = \<^assert> (facts_under \<^theory> "Test5_Propagation_Sublocale.Ic." =
  ["Test5_Propagation_Sublocale.Ic.LFc_axioms", "Test5_Propagation_Sublocale.Ic.cb_axioms",
   "Test5_Propagation_Sublocale.Ic.cc_axioms"])\<close>

end
