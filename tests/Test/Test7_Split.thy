(* Plan section 7 test 7: [split del] in a light block with a predicate is global -- in the
   downstream session the case over tsp is no longer split by simp, while the heavy twin's
   deletion of tsplit2 is not seen here. *)
theory Test7_Split
  imports Test_Support "Light_Locale_Base.Base_Split"
begin

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
fun splits prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => simp_tac context 1)) ();
(*simp proves these only by splitting the case: tsp's rule was deleted globally by the light block,
  tsp2's only inside the heavy twin's locale*)
val _ = \<^assert> (not (splits \<^prop>\<open>(case t of A \<Rightarrow> (0::nat) | B \<Rightarrow> 0) = 0\<close>));
val _ = \<^assert> (splits \<^prop>\<open>(case t of A2 \<Rightarrow> (0::nat) | B2 \<Rightarrow> 0) = 0\<close>);
\<close>

end
