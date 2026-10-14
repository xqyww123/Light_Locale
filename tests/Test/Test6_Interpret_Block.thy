(* Plan section 7 test 6, interpret I: LF T inside a declaration-block proof (plan lines
   4395-4400): after foo [simp] and inductive ev in the block, a lemma assuming cring T interprets
   I: LF T; "using I.LF_axioms h proof (cases rule: LF.ev.cases)" works, "using h proof cases" falls
   to case_split and case zero is undefined.  The simp rows about the instance T are milestone 3
   (the solver) except the [OF I.LF_axioms] form, exercised by the cases row. *)
theory Test6_Interpret_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  gc :: "nat \<Rightarrow> nat"  hc :: "nat \<Rightarrow> nat"
axiomatization where Pc_ax: "Pc x y" and gc_hc: "gc (hc n) = n"

context LF begin
lemma foo [simp]: "gc (hc n) = n" by (rule gc_hc)
inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0" | step: "ev n \<Longrightarrow> ev (Suc (Suc n))" | pin: "Pc S (7::nat) \<Longrightarrow> ev 7"
lemma
  fixes T :: "nat ring" and n :: nat
  assumes T: "cring T" and h: "LF.ev T n"
  shows "LF.ev T n"
proof -
  interpret I: LF T by (simp add: LF_def UP_cring_def T)
  ML_prf \<open>
    val ctxt = \<^context>;
    fun run facts method goal = proof_after {apply = false} ctxt facts method (Syntax.read_prop ctxt goal);
    val goal = "gc (hc 0) = 0";
    (* the bare simp sees the block copy foo, which is about S, not T: here the goal is about neither,
       so the row's goal mentions T through ev *)
    val _ = \<^assert> (can (fn () => run [@{thm I.LF_axioms}, @{thm h}] "cases rule: LF.ev.cases" "W n") ());
    val st = run [@{thm h}] "cases" "W n";
    val _ = \<^assert> (case_names st = ["True", "False"]);
    val _ = \<^assert> ((Proof_Context.check_case (Proof.context_of st) true ("zero", Position.none) []; false)
      handle ERROR msg => String.isPrefix "Undefined case" (XML.content_of (YXML.parse_body msg)));
  \<close>
  show ?thesis by (rule h)
qed
end

end
