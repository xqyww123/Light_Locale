(* Plan section 7 test 9 (structure), plan 5199-5231: the header route never overwrites a live
   implicit structure.  (a) interpretation inside the light block: the bare one in the instance
   is read through LF's implicit structure UP S and replaced by the stage-1000 step, nothing
   writes the placeholder; (b) the same inside a proof after with_implicit_structure "S": the
   instance is one of S.  Registrations are read inside the block (interpretation.ML:227-230). *)
theory Test9_XO
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;

(*the registrations of XO in this context: no placeholder anywhere, one with the expected second
  instance (the proof below also sees the block's registration)*)
fun instances_are ctxt expected =
  let
    val thy = Proof_Context.theory_of ctxt;
    val instss =
      map (Locale.instance_of thy (loc thy "XO") o #2)
        (Locale.registrations_of (Context.Proof ctxt) (loc thy "XO"));
  in
    \<^assert> (not (exists (exists has_placeholder) instss));
    \<^assert> (exists (fn insts => Term.aconv_untyped (nth insts 1, expected)) instss)
  end;
\<close>

context LF
begin

(* the row inside a proof without with_implicit_structure, before the block's interpretation so
   that the proof's registration is the only one: the block's UP S *)
lemma "True"
proof -
  interpret U: XO S "\<one>"
    using LF_axioms unfolding XO_def LFr2_def LF_def .
  ML_prf \<open>
    val thy = \<^theory>;
    val insts =
      Locale.instance_of thy (loc thy "XO")
        (#2 (the_single (Locale.registrations_of (Context.Proof \<^context>) (loc thy "XO"))));
    val _ = \<^assert> (not (exists has_placeholder insts));
    val _ = \<^assert> (Term.aconv_untyped (nth insts 1,
      Const (\<^const_name>\<open>one\<close>, dummyT) $ (Const (\<^const_name>\<open>UP\<close>, dummyT) $ Free ("S", dummyT))));
  \<close>
  show True ..
qed

interpretation U: XO S "\<one>"
  using LF_axioms unfolding XO_def LFr2_def LF_def .

ML_val \<open>
instances_are \<^context>
  (Const (\<^const_name>\<open>one\<close>, dummyT) $ (Const (\<^const_name>\<open>UP\<close>, dummyT) $ Free ("S", dummyT)));
\<close>

lemma "True"
proof -
  with_implicit_structure "S"
  interpret U: XO S "\<one>"
    using LF_axioms unfolding XO_def LFr2_def LF_def .
  ML_prf \<open>
    instances_are \<^context> (Const (\<^const_name>\<open>one\<close>, dummyT) $ Free ("S", dummyT));
  \<close>
  show True ..
qed

end

end
