(* Plan section 7 test 12 (repair phase, step 1), rule R's variable condition on type variables
   (batch-1 plan section 4.1, B3): after interpretation I: LFs "{}::nat set", u2t (whose ?'a also
   occurs in the conclusion) is returned unchanged, u1 (?'a only in the premise) is discharged. *)
theory Test12_TVar
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"
lemma (in LFs) u2t: "(x::'a) = x" by (rule refl)
lemma (in LFs) u1: "(x::'b) = x" by (rule refl)

interpretation I: LFs "{}::nat set" by (rule LFs.intro) simp

ML \<open>
check_rows
 [("u2t", fn () => unchanged \<^context> @{thm LFs.u2t}),
  ("u1", fn () => discharges \<^context> 1 @{thm LFs.u1})]
\<close>

end
