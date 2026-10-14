(* Light locale test fixtures (plan section 7, preface): the gate fixture LF with its heavy twin D
   and the auxiliary pair LM/DM.  Each heavy twin is declared with the byte-identical header text
   of its light fixture -- only the command word and the name differ -- which pins the parameter
   names, the type-variable names and the variable-structure table.  No global declaration lives
   here: a test row that needs one gets its own theory in this session (plan section 7, theory
   layout). *)
theory Light_Locale_Base
  imports "Light_Locale.Light_Locale" "HOL-Algebra.UnivPoly"
begin

(* Gate fixture of tests 6, 8 and 9.  UP_cring's P (structure) is eliminated (P == UP S), R is
   re-fixed as S without a mark, so the first-layer structure table is empty; the implicit
   structure is UP S (milestone 2). *)
light_locale LF = UP_cring S for S

locale D = UP_cring S for S

(* Auxiliary pair for test 6's bare \<otimes> clauses: monoid's G (structure) is neither instantiated nor
   eliminated, so the first-layer table is [G] on both sides. *)
light_locale LM = monoid

locale DM = monoid

end
