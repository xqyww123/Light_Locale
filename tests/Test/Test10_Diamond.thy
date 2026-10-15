(* Plan section 7 test 10 (sublocale from a light locale), the diamond with a light-edge rewrites
   (plan lines 5319-5320): the same shape built once as light_locale LFd = B and once as locale
   LFh = B, each with the edge sublocale ... <= e: C "u + 1" rewrites "u + 1 + 0 = u + 1"; the
   other side of the diamond, K, reaches the very instance C (u + 1) through an ordinary path under
   the same qualifier, so that in H = LFd + K / K + LFd the instance arrives twice and decision 15's
   first-arrival rule decides which morphism its theorems get.  In both import orders context H
   gives the theorem e.cl of that instance -- its statement contains the rewrite's left-hand side --
   the same Thm.prop_of between the light and the heavy version (the two orders are not compared
   with each other).  Fixture guard: on the heavy side the two orders differ, so the rewrites really
   decide the compared theorem. *)
theory Test10_Diamond
  imports Test_Support
begin

locale B = fixes u :: nat assumes bu: "u = u"
locale C = fixes v :: nat assumes cv: "v = v"
lemma (in C) cl: "v + 0 = v" by simp
light_locale LFd = B
locale LFh = B
sublocale LFd \<subseteq> e: C "u + 1" rewrites "u + 1 + 0 = u + 1" by unfold_locales simp_all
sublocale LFh \<subseteq> e: C "u + 1" rewrites "u + 1 + 0 = u + 1" by unfold_locales simp_all
locale K = e: C "u + 1" for u :: nat
locale H1 = LFd + K
locale H2 = K + LFd
locale H1h = LFh + K
locale H2h = K + LFh

ML \<open>
fun cl_of l =
  Thm.prop_of (Proof_Context.get_thm (Locale.init (Locale.check_global \<^theory> (l, Position.none)) \<^theory>) "e.cl");
val _ = \<^assert> (not (cl_of "H1h" aconv cl_of "H2h"));
val _ = \<^assert> (cl_of "H1" aconv cl_of "H1h");
val _ = \<^assert> (cl_of "H2" aconv cl_of "H2h");
\<close>

end
