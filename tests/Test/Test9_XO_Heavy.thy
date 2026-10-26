(* Plan section 7 test 9 (structure), plan 5214-5215: the heavy twin of Test9_XO -- the
   interpretation in context D and in a proof, the instance written with its index. *)
theory Test9_XO_Heavy
  imports Test9_Fixtures
begin

context D
begin

interpretation U: XO S "\<one>\<^bsub>UP S\<^esub>"
  by unfold_locales

ML \<open>local
val thy = \<^theory>;
val regs = Locale.registrations_of (Context.Proof \<^context>) (Test_Support.loc thy "XO");
val _ = \<^assert> (not (exists Test_Support.has_placeholder
  (Locale.instance_of thy (Test_Support.loc thy "XO") (#2 (the_single regs)))));
in end\<close>

lemma "True"
proof -
  interpret U: XO S "\<one>\<^bsub>UP S\<^esub>" by unfold_locales
  ML_prf \<open>
    val thy = \<^theory>;
    val _ = \<^assert> (not (exists (exists Test_Support.has_placeholder)
      (map (Locale.instance_of thy (Test_Support.loc thy "XO") o #2)
        (Locale.registrations_of (Context.Proof \<^context>) (Test_Support.loc thy "XO")))));
  \<close>
  show True ..
qed

end

end
