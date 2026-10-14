(* Plan section 7 test 6, the inductive_set row (plan line 4464-4468): a block inductive_set whose
   third rule mentions S is stored as LF.Evs ?S; in the reopened block, with hs: n \<in> LF.Evs S,
   "using LF_axioms hs proof (cases n)" prints the cases of the heavy twin's "using hs proof (cases n)"
   (the instantiation goes to ?a, ?S in the exported premises takes no part).  The stock warning
   "Ignoring malformed set / predicate conversion rule" of the theory-level pass is not asserted. *)
theory Test6_Cases_Set
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

ML \<open>
fun run ctxt facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
val texts = Unsynchronized.ref ([]: string list);
\<close>

context D begin
inductive_set Evs :: "nat set" where "0 \<in> Evs" | "n \<in> Evs \<Longrightarrow> Suc (Suc n) \<in> Evs" | "Pc S (7::nat) \<Longrightarrow> 7 \<in> Evs"
end
context D begin
ML \<open>
val (hs, ctxt) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "hs" "n \<in> Evs";
val _ = texts := cases_text (run ctxt [hs] "cases n" "W n");
\<close>
end

context LF begin
inductive_set Evs :: "nat set" where "0 \<in> Evs" | "n \<in> Evs \<Longrightarrow> Suc (Suc n) \<in> Evs" | "Pc S (7::nat) \<Longrightarrow> 7 \<in> Evs"
end
context LF begin
ML_val \<open>
val (hs, ctxt) = assume_in \<^context> [("n", \<^typ>\<open>nat\<close>)] "hs" "n \<in> LF.Evs S";
val _ = \<^assert> (cases_text (run ctxt [@{thm LF_axioms}, hs] "cases n" "W n") = ! texts);
\<close>
end

end
