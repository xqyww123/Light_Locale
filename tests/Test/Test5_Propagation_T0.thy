(* The declarations shared by the two propagation order pairs of plan section 7 test 5 (plan line
   4205-4206: the edge before / after the interpretation, with sublocale LF <= B2 s and with an
   edge added to H; "both orders give the same result" is a comparison over one fixture): no
   registration and no global declaration (plan preface 3838). *)
theory Test5_Propagation_T0
  imports Test_Support
begin

locale T = fixes z :: nat assumes "z = z"
lemma (in T) tt: "z + 0 = z" by simp
abbreviation (in T) ta where "ta \<equiv> z + 1"
consts t :: nat
light_locale LF = T

end
