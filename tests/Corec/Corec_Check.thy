(* Plan section 7 test 1: every named fact of HOL-Corec_Examples (HOL/ROOT:966-986).  The session
   reloads those theories from source, so on the patched tree they are proved by the patched Pure. *)
theory Corec_Check
  imports
    "HOL-Corec_Examples.LFilter"
    "HOL-Corec_Examples.Paper_Examples"
    "HOL-Corec_Examples.Stream_Processor"
    "HOL-Corec_Examples.Simple_Nesting"
    "HOL-Corec_Examples.Iterate_GPV"
    "HOL-Corec_Examples.GPV_Bare_Bones"
    "HOL-Corec_Examples.Merge_D"
    "HOL-Corec_Examples.Merge_Poly"
    "HOL-Corec_Examples.Misc_Mono"
    "HOL-Corec_Examples.Misc_Poly"
    "HOL-Corec_Examples.Small_Concrete"
    "HOL-Corec_Examples.Stream_Friends"
    "HOL-Corec_Examples.TLList_Friends"
    "HOL-Corec_Examples.Type_Class"
begin

ML_file "../Golden/golden.ML"

ML \<open>Golden.check \<^theory> "corec_examples_facts.golden" (Golden.facts_dump \<^theory> "HOL-Corec_Examples.")\<close>

end
