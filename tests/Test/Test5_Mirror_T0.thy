(* The declarations shared by the mirror-pair leaves of plan section 7 test 5 (plan lines 4150-4157,
   4171-4175; rows A, A+C, A+C+B, B, B+C and their heavy twins): no registration and no global
   declaration (plan preface 3838).  Each leaf declares only its own LF (light) or LFh (heavy) and
   its H, so that the rows' item-by-item comparisons are over one fixture. *)
theory Test5_Mirror_T0
  imports Test_Support
begin

locale HP = fixes y :: nat assumes hp: "y = y"
lemma (in HP) hpl: "y + 0 = y" by simp
locale HB = HP x for x + assumes hb: "x = x"
abbreviation (in HB) hba where "hba \<equiv> x + 1"
consts c :: nat
locale K = HB
locale M = HB c

end
