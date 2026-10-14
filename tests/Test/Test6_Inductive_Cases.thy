(* Plan section 7 test 6, inductive_cases and its relatives on a block inductive (plan lines
   4680-4700): (a) inductive_cases succeeds in the declaration block (the local ip.cases) and in
   the reopened block, where the stored result has LF ?S first, the premise count of the twin's
   reopened result, is phi-equal to it and has no other premise LF ?S; (b) at theory level on a
   free instance the result starts with the proposition and then LF ?p, with the premise count of
   (a) and K 0, erule leaves LF p as the first new subgoal, [OF LF_axioms] on it in the reopened
   block has no unifier, and the heavy twin's theory-level inductive_cases is refused;
   inductive_simps and fun_cases succeed in the declaration block and fail in the reopened one,
   the_inductive_global by full name (print_inductives' own reader) knows LF.ip only in the
   declaration block, code_pred fails in both; a hand-written inversion lemma is phi-equal to the
   twin's inductive_cases; the ind_cases method in the three settings beside inductive_cases. *)
theory Test6_Inductive_Cases
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

ML \<open>
(*the thunk fails and its message (whatever the exception) starts with the prefix*)
fun fails_with prefix f =
  (case Exn.capture f () of
    Exn.Exn exn => String.isPrefix prefix (Protocol_Message.clean_output (Runtime.exn_message exn))
  | Exn.Res _ => false);
val natT = \<^typ>\<open>nat\<close>;
(*row (a) on a stored result: LF ?S first, the twin's premise count, phi-equal to it, exactly one
  light premise*)
fun stored_ok ctxt (thl, thh) =
  Light_Locale_Axiom_Facts.is_light_prop ctxt (hd (Thm.prems_of thl)) andalso
  Thm.nprems_of thl = Thm.nprems_of thh andalso
  phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (thl, thh) andalso
  length (light_prems ctxt thl) = 1;
(*the ind_cases method on the goal, by the number of subgoals it leaves*)
fun ind_cases_subgoals ctxt prop goal =
  subgoals (run_apply (fix_in ctxt [("n", natT)]) [] ("ind_cases \"" ^ prop ^ "\"") goal);
fun code_pred_fails lthy name =
  not (can (fn () => Predicate_Compile_Core.code_pred_cmd Predicate_Compile_Aux.default_options name lthy) ());
fun inductive_simps_cmd lthy name prop =
  Inductive.inductive_simps_cmd [((Binding.name name, []), [prop])] false lthy;
fun fun_cases_cmd lthy name prop = Fun_Cases.fun_cases_cmd [((Binding.name name, []), [prop])] lthy;
fun inductive_cases_cmd lthy name prop =
  Inductive.inductive_cases_cmd [((Binding.name name, []), [prop])] false lthy;
\<close>

section \<open>The heavy twin\<close>

context D begin
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
fun f :: "nat \<Rightarrow> nat" where "f 0 = 0" | "f (Suc n) = f n"
inductive_cases ipE: "ip (Suc n)"
inductive_simps ipS: "ip (Suc n)"
fun_cases fC: "f n = m"
ML \<open>
val heavy_ipE = @{thm ipE};
val heavy_ind_cases_decl = ind_cases_subgoals \<^context> "ip (Suc n)" "ip (Suc n) \<Longrightarrow> W";
\<close>
ML_val \<open>\<^assert> (code_pred_fails \<^context> "D.ip")\<close>
end
context D begin
inductive_cases ipE2: "ip (Suc n)"
inductive_simps ipS2: "ip (Suc n)"
ML \<open>val heavy_ind_cases_reopened = ind_cases_subgoals \<^context> "ip (Suc n)" "ip (Suc n) \<Longrightarrow> W";\<close>
end
ML \<open>
val _ = \<^assert> (fails_with "Proposition not an inductive predicate"
  (fn () => inductive_cases_cmd (Named_Target.theory_init \<^theory>) "ipE3h" "D.ip p (Suc n)"));
\<close>

section \<open>The light block\<close>

context LF begin
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
fun f :: "nat \<Rightarrow> nat" where "f 0 = 0" | "f (Suc n) = f n"
inductive_cases ipE: "ip (Suc n)"
inductive_simps ipS: "ip (Suc n)"
fun_cases fC: "f n = m"
ML_val \<open>
val _ = \<^assert> (three_items (@{thm ipE}, heavy_ipE));
val _ = \<^assert> (ind_cases_subgoals \<^context> "ip (Suc n)" "ip (Suc n) \<Longrightarrow> W" = heavy_ind_cases_decl);
val _ = \<^assert> (can (Inductive.the_inductive_global \<^context>) \<^const_name>\<open>LF.ip\<close>);
val _ = \<^assert> (code_pred_fails \<^context> "LF.ip");
\<close>
end

ML \<open>
(* (a) the stored result of the declaration block *)
val _ = \<^assert> (stored_ok \<^context> (@{thm LF.ipE}, @{thm D.ipE}));
\<close>

(* (b) at theory level, on a free instance *)
inductive_cases ipE3: "LF.ip p (Suc n)"
ML \<open>
val ps = Thm.prems_of @{thm ipE3};
(* the proposition first, then LF ?p *)
val _ = \<^assert> (same_shape (Logic.mk_implies (nth ps 0, nth ps 1), Logic.varify_global \<^prop>\<open>LF.ip p (Suc n) \<Longrightarrow> LF p\<close>));
val _ = \<^assert> (length (light_prems \<^context> @{thm ipE3}) = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm ipE3} = 0);
val _ = \<^assert> (Thm.nprems_of @{thm ipE3} = Thm.nprems_of @{thm LF.ipE});
(* erule ipE3, and the ind_cases method: LF p is the first new subgoal *)
val ctxt = #2 (Proof_Context.add_fixes [(Binding.name "p", NONE, NoSyn), (Binding.name "n", SOME natT, NoSyn)] \<^context>);
val _ = List.app (fn method =>
    let val st = run_apply ctxt [] method "LF.ip p (Suc n) \<Longrightarrow> W"
    in \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt (hd (goal_prems st))) end)
  ["erule ipE3", "ind_cases \"LF.ip p (Suc n)\""];
\<close>

section \<open>The reopened light block\<close>

context LF begin
inductive_cases ipE2: "LF.ip S (Suc n)"
lemma ipE': "LF.ip S (Suc n) \<Longrightarrow> (Pc S n \<Longrightarrow> LF.ip S n \<Longrightarrow> W) \<Longrightarrow> W"
  by (erule LF.ip.cases[OF LF_axioms]) auto
ML_val \<open>
val _ = \<^assert> ((@{thm ipE3} OF [@{thm LF_axioms}]; false) handle THM (msg, _, _) => String.isPrefix "OF: no unifiers" msg);
(* the ind_cases method in the reopened block, nothing chained: the twin's subgoal count *)
val _ = \<^assert> (ind_cases_subgoals \<^context> "LF.ip S (Suc n)" "LF.ip S (Suc n) \<Longrightarrow> W" = heavy_ind_cases_reopened);
(* a plain ERROR (inductive.ML:663): the leading text of the message, plan line 4693's "is not
   unique" being its end *)
val _ = \<^assert> ((inductive_simps_cmd \<^context> "ipS2" "LF.ip S (Suc n)"; false)
  handle ERROR msg => String.isPrefix "equations matching pattern" (Protocol_Message.clean_output msg));
val _ = \<^assert> (fails_with "Proposition is not a function equation:" (fn () => fun_cases_cmd \<^context> "fC2" "LF.f n = m"));
val _ = \<^assert> (not (can (Inductive.the_inductive_global \<^context>) \<^const_name>\<open>LF.ip\<close>));
val _ = \<^assert> (code_pred_fails \<^context> "LF.ip");
\<close>
end

ML \<open>
val _ = \<^assert> (stored_ok \<^context> (@{thm LF.ipE2}, @{thm D.ipE2}));
(* the hand-written inversion lemma *)
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm LF.ipE'}, @{thm D.ipE2}));
\<close>

end
