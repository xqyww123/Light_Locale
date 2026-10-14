(* Plan section 7 test 4 (upgrade): the shared fixtures of the test-4 leaves -- the heavy locale HB
   with an assumption, an abbreviation and a lemma, the instance t, and the one-parameter heavy
   locale HQ whose abbreviation mentions its parameter.  No registration lives here; each leaf
   declares its own light_locale LF = HB and its own edges. *)
theory Test4_Fixture
  imports Test_Support
begin

locale HB = fixes x :: nat assumes hb: "x = x"

abbreviation (in HB) hba where "hba \<equiv> x + 1"

lemma (in HB) hb2: "x + 0 = x" by simp

consts t :: nat

locale HQ = fixes y :: nat assumes hq: "y = y"

abbreviation (in HQ) hqa where "hqa \<equiv> y + 1"

(* the stand-in of the padic instance for the one-goal row: one defines equation and one
   assumption (plan section 11, implementation-period change (12)) *)
locale HD = fixes z :: nat and y :: nat defines "z \<equiv> Suc y" assumes hd: "y = y"

ML \<open>
(*the base names a full interpretation of HB t installs (Test4_Control measures it)*)
val hb_installed = ["HB_axioms", "hb", "hb2"];


\<close>

end
