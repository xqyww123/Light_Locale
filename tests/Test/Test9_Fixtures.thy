(* Plan section 7 test 9 (structure): the fixture list of plan 5115-5124 and the further fixtures
   other rows of test 9 name (LFr/LFr2 5136-5137, M1 5139, H/H' 5152, XO 5201-5203, UPl/LFl/Dl
   5236-5237, LS for the sibling leaves) -- declarations only, so every test 9 leaf may import
   them.  The (structure) parameters take ('a, 'b) monoid_scheme except Cm's bare type variable;
   f and tmk are the constants of the plan's fixture list; A and B both fix G (structure).  At
   the end, the attribute and the rule the header rows with attributes use as arguments. *)
theory Test9_Fixtures
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

consts
  f :: "('a, 'b) monoid_scheme \<Rightarrow> ('a, 'b) monoid_scheme"
  tmk :: "'q \<Rightarrow> ('a, 'b) ring_scheme"

locale Gm = fixes G :: "('a, 'b) monoid_scheme" (structure)
locale Bm = fixes G :: "('a, 'b) monoid_scheme" (structure)
locale Bt = fixes T :: "('a, 'b) monoid_scheme" (structure)
locale Pm = fixes P :: "('a, 'b) monoid_scheme" (structure)
locale Cm = fixes C :: 'c (structure)
locale A = fixes G :: "('a, 'b) monoid_scheme" (structure)
locale B = fixes G :: "('a, 'b) monoid_scheme" (structure)

(* UPm imitates UP: P (structure) is defined on R (structure) *)
locale UPm =
  fixes R :: "('a, 'b) monoid_scheme" (structure) and P :: "('a, 'b) monoid_scheme" (structure)
  defines "P \<equiv> f R"
locale UPm2 =
  fixes R :: "('a, 'b) monoid_scheme" (structure) and P :: "('a, 'b) monoid_scheme" (structure)
    and T :: "('a, 'b) monoid_scheme" (structure)
  defines "P \<equiv> f R"
locale UPr =
  fixes P :: "('a, 'b) monoid_scheme" (structure) and R :: "('a, 'b) monoid_scheme" (structure)
  defines "P \<equiv> f R"
locale UPc =
  fixes R :: "('a, 'b) monoid_scheme" (structure) and P :: "('a, 'b) monoid_scheme" (structure)
    and Q :: "('a, 'b) monoid_scheme" (structure)
  defines "P \<equiv> f R" and "Q \<equiv> f P"
locale UPc2 =
  fixes R :: "('a, 'b) monoid_scheme" (structure) and P :: "('a, 'b) monoid_scheme"
    and Q :: "('a, 'b) monoid_scheme" (structure)
  defines "P \<equiv> f R" and "Q \<equiv> f P"

light_locale LU = UPm
light_locale LU2 = UPm2
light_locale LFr = UP_cring R for R
light_locale LFr2 = UP_cring
locale M1 = LU S for S (structure)
locale H' = LF + A
locale H = A + LF

(* the header route's fixture (plan 5201-5203): LFr2 instantiated, a type variable of its own *)
locale XO = LFr2 S for S + fixes a :: 'z

(* the placeholder-type fixture (plan 5236-5237): an expansion with a binder; the light child and
   its heavy twin (Test9_Header, Test9_Header_Attribute row 7, Test9_Header_Implicit row 21) *)
locale UPl =
  fixes R :: "('a, 'b) monoid_scheme" (structure) and M :: "('a, 'b) monoid_scheme" (structure)
  defines "M \<equiv> R\<lparr>mult := \<lambda>x y. x\<rparr>"
light_locale LFl = UPl S for S
locale Dl = UPl S for S

(* the header-declared light locale the sibling leaves (Test9_Sib_A/B/AB/BA) add abbreviations
   to: its header's S beats the cut UP S and survives the merge of the two sibling theories *)
light_locale LS = UP_cring S for S + implicit_structure S

(* the attribute arguments of the header rows with attributes (Test9_Header_Attribute,
   Test9_Header_Implicit row 13): t9_premise reads its term once, as Args.term does, and the token keeps
   it; t9_premise_rule[where x = ...] reads its string again wherever the attribute is applied.
   Both put a premise t = t in front, so the two readings meet in one theorem. *)
attribute_setup t9_premise =
  \<open>Args.term >> (fn t => Thm.rule_attribute [] (fn context =>
    Thm.implies_intr (Thm.cterm_of (Context.proof_of context) (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t))))))\<close>
lemma t9_premise_rule: "PROP P \<Longrightarrow> x = x \<Longrightarrow> PROP P" by assumption

end
