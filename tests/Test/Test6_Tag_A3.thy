(* Plan section 7 test 6 (plan line 4660): the row-level "for" on a fact recognised only by its
   tag -- lemmas fooN3 [dest] = SetN.fooN[of y] for y in a reopened context SetN: K 0 (the block's
   premise_count is 0, nothing is added), the derived dest rule's major premise is 0 < ?y, the
   former exported premise.  Its own leaf: fooN1 [dest] of leaf A registers the same proposition. *)
theory Test6_Tag_A3
  imports Test_Support
begin

ML \<open>open Test_Support\<close>
consts Qn :: "nat \<Rightarrow> bool"  Rn :: "nat \<Rightarrow> bool"  Rn' :: "nat \<Rightarrow> bool"
axiomatization where qr: "0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n \<and> Rn' n"

light_locale SetN = fixes n :: nat
context SetN begin
context assumes hn: "0 < n" begin
lemma fooN: "Qn n \<Longrightarrow> Rn n \<and> Rn' n" by (rule qr[OF hn])
end
end

context SetN begin
lemmas fooN3 [dest] = SetN.fooN[of y] for y
end
ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm SetN.fooN3} = 0);
val _ = \<^assert> (exists (fn (_, plain, _) =>
    (case HOLogic.dest_Trueprop (Thm.major_prem_of plain) of
      Const (\<^const_name>\<open>less\<close>, _) $ _ $ Var _ => true | _ => false))
  (claset_entries \<^context> @{thm SetN.fooN3}));
\<close>

end
