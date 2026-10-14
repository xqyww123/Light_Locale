(* Plan section 7 test 10 (sublocale from a light locale), the diamond with a light-edge rewrites:
   the same shape built once as light_locale LFd = B and once as locale LFh = B, each with the edge
   sublocale ... <= e: C (u + 1) rewrites "u + 1 + 0 = u + 1"; in both import orders context H begin
   gives the theorem bl of B u the same Thm.prop_of between the light and the heavy version
   (the two orders are not compared with each other). *)
theory Test10_Diamond
  imports Test_Support
begin

locale B = fixes u :: nat assumes bu: "u = u"
lemma (in B) bl: "u + 0 = u" by simp
locale C = fixes v :: nat assumes cv: "v = v"
lemma (in C) cl: "v + 0 = v" by simp
light_locale LFd = B
locale LFh = B
sublocale LFd \<subseteq> e: C "u + 1" rewrites "u + 1 + 0 = u + 1" by unfold_locales simp_all
sublocale LFh \<subseteq> e: C "u + 1" rewrites "u + 1 + 0 = u + 1" by unfold_locales simp_all
locale K = B
locale H1 = LFd + K
locale H2 = K + LFd
locale H1h = LFh + K
locale H2h = K + LFh

ML \<open>
fun bl_of l = Thm.prop_of (Proof_Context.get_thm (Locale.init (Locale.check_global \<^theory> (l, Position.none)) \<^theory>) "bl");
val _ = \<^assert> (bl_of "H1" aconv bl_of "H1h");
val _ = \<^assert> (bl_of "H2" aconv bl_of "H2h");
\<close>

end
