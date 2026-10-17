(* Plan section 7 test 9 (structure), plan 5209-5213: the theory-level sublocale variant of
   Test9_XO's row (a) -- its instances are read in LF's context, where Locale.init installed the
   implicit structure; it adds a permanent dependency edge to the gate fixture, hence its own
   leaf.  The assertion is on that edge's instances, not on a registration. *)
theory Test9_XO_Sub
  imports Test9_Fixtures
begin

sublocale LF \<subseteq> U: XO S "\<one>"
  using LF_axioms unfolding XO_def LFr2_def LF_def .

ML \<open>
val thy = \<^theory>;
val insts = Test_Support.instances thy "XO" "LF";
val _ = \<^assert> (not (exists Test_Support.has_placeholder insts));
val _ = \<^assert> (Term.aconv_untyped (nth insts 1,
  Const (\<^const_name>\<open>one\<close>, dummyT) $ (Const (\<^const_name>\<open>UP\<close>, dummyT) $ Free ("S", dummyT))));
\<close>

end
