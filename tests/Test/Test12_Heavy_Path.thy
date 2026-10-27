(* Plan section 7 test 12 (repair phase, step 1), the heavy intermediary (batch-1 plan section 4.1,
   A9; master plan lines 5342-5352): light LF2 = H, heavy H = LFs + fixes k.  The block of LF2
   holds LFs_axioms (the opening path); after interpretation I: LF2 "{0::nat}" 0 the theory's
   table holds I.LFs_axioms (theory-level syntax-only reach through the light edge LF2 -> H). *)
theory Test12_Heavy_Path
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"
locale H = LFs + fixes k :: nat
light_locale LF2 = H

context LF2 begin
ML \<open>check_rows [("A9 block", fn () => retrieves_only \<^context> \<^prop>\<open>LFs S\<close> @{thm LFs_axioms})]\<close>
end

interpretation I: LF2 "{0::nat}" 0 unfolding LF2_def H_def by (rule LFs.intro) simp

ML \<open>check_rows [("A9 theory", fn () => retrieves_only \<^context> \<^prop>\<open>LFs {0::nat}\<close> @{thm I.LFs_axioms})]\<close>

end
