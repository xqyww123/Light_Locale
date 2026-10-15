(* Plan section 7 test 7 (plan line 4803): [split del] in a light block with a predicate is
   global -- in the downstream session the case over tsp is no longer split by simp, while the
   heavy twin's deletion of tsplit2 takes effect only where its locale Dsp is activated: not at
   theory level (the control), but inside Dsp's context. *)
theory Test7_Split
  imports Test_Support "Light_Locale_Base.Base_Split"
begin

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*simp proves these only by splitting the case: tsp's rule was deleted globally by the light block,
  tsp2's only inside the heavy twin's locale*)
val _ = \<^assert> (not (Test_Support.by_simp ctxt \<^prop>\<open>(case t of A \<Rightarrow> (0::nat) | B \<Rightarrow> 0) = 0\<close>));
val _ = \<^assert> (Test_Support.by_simp ctxt \<^prop>\<open>(case t of A2 \<Rightarrow> (0::nat) | B2 \<Rightarrow> 0) = 0\<close>);
val dsp = Named_Target.init [] (Locale.check_global \<^theory> ("Dsp", Position.none)) \<^theory>;
val _ = \<^assert> (not (Test_Support.by_simp dsp \<^prop>\<open>(case t of A2 \<Rightarrow> (0::nat) | B2 \<Rightarrow> 0) = 0\<close>));
\<close>

end
