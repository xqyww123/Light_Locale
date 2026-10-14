(* Plan section 7 test 6, inductive_cases and its relatives on a block inductive (plan lines
   4680-4700): (a) inductive_cases succeeds in the declaration block (the local ip.cases) and in
   the reopened block, where the stored result has LF ?S first, the premise count of the twin's
   reopened result, is phi-equal to it and has no other premise LF ?S; (b) at theory level on a
   free instance the result starts with the proposition and then LF ?p, with the premise count of
   (a) and K 0, erule leaves LF p as the first new subgoal, [OF LF_axioms] on it in the reopened
   block has no unifier, and the heavy twin's theory-level inductive_cases is refused;
   inductive_simps and fun_cases succeed in the declaration block and fail in the reopened one,
   the_inductive (what print_inductives lists) knows ip only in the declaration block, code_pred
   fails in both; a hand-written inversion lemma is phi-equal to the twin's inductive_cases. *)
theory Test6_Inductive_Cases
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a
axiomatization where Pc_ax: "Pc x y"

ML \<open>
fun plain msg = XML.content_of (YXML.parse_body msg);
(*the thunk fails and its message (whatever the exception) starts with the prefix*)
fun fails_with prefix f =
  (case Exn.capture f () of
    Exn.Exn exn => String.isPrefix prefix (plain (Runtime.exn_message exn))
  | Exn.Res _ => false);
val natT = \<^typ>\<open>nat\<close>;
fun light_prems ctxt th = filter (Light_Locale_Axiom_Facts.is_light_prop ctxt) (Thm.prems_of th);
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
ML \<open>val heavy_ipE = @{thm ipE};\<close>
ML_val \<open>\<^assert> (code_pred_fails \<^context> "D.ip")\<close>
end
context D begin
inductive_cases ipE2: "ip (Suc n)"
inductive_simps ipS2: "ip (Suc n)"
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
val _ = \<^assert> (can (Inductive.the_inductive \<^context>) \<^term>\<open>ip\<close>);
val _ = \<^assert> (code_pred_fails \<^context> "LF.ip");
\<close>
end

ML \<open>
(* (a) the stored result of the declaration block *)
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.ipE})));
val _ = \<^assert> (Thm.nprems_of @{thm LF.ipE} = Thm.nprems_of @{thm D.ipE});
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm LF.ipE}, @{thm D.ipE}));
val _ = \<^assert> (length (light_prems \<^context> @{thm LF.ipE}) = 1);
\<close>

(* (b) at theory level, on a free instance *)
inductive_cases ipE3: "LF.ip p (Suc n)"
ML \<open>
val ps = Thm.prems_of @{thm ipE3};
val _ = \<^assert> (HOLogic.dest_Trueprop (hd ps) |> Term.head_of |> (fn Const (c, _) => Long_Name.base_name c = "ip" | _ => false));
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (nth ps 1));
val _ = \<^assert> (length (light_prems \<^context> @{thm ipE3}) = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm ipE3} = 0);
val _ = \<^assert> (Thm.nprems_of @{thm ipE3} = Thm.nprems_of @{thm LF.ipE});
(* erule: LF p is the first new subgoal *)
val ctxt = #2 (Proof_Context.add_fixes [(Binding.name "p", NONE, NoSyn), (Binding.name "n", SOME natT, NoSyn)] \<^context>);
val st = proof_after {apply = true} ctxt [] "erule ipE3" (Syntax.read_prop ctxt "LF.ip p (Suc n) \<Longrightarrow> W");
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop ctxt (hd (Thm.prems_of (#goal (Proof.goal st)))));
\<close>

section \<open>The reopened light block\<close>

context LF begin
inductive_cases ipE2: "LF.ip S (Suc n)"
lemma ipE': "LF.ip S (Suc n) \<Longrightarrow> (Pc S n \<Longrightarrow> LF.ip S n \<Longrightarrow> W) \<Longrightarrow> W"
  by (erule LF.ip.cases[OF LF_axioms]) auto
ML_val \<open>
val _ = \<^assert> ((@{thm ipE3} OF [@{thm LF_axioms}]; false) handle THM (msg, _, _) => String.isPrefix "OF: no unifiers" msg);
val _ = \<^assert> ((case Exn.capture (fn () => inductive_simps_cmd \<^context> "ipS2" "LF.ip S (Suc n)") () of
    Exn.Exn exn => String.isSubstring "is not unique" (plain (Runtime.exn_message exn))
  | Exn.Res _ => false));
val _ = \<^assert> (fails_with "Proposition is not a function equation:" (fn () => fun_cases_cmd \<^context> "fC2" "LF.f n = m"));
val _ = \<^assert> (not (can (Inductive.the_inductive \<^context>) \<^term>\<open>LF.ip S\<close>));
val _ = \<^assert> (code_pred_fails \<^context> "LF.ip");
\<close>
end

ML \<open>
val _ = \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.ipE2})));
val _ = \<^assert> (Thm.nprems_of @{thm LF.ipE2} = Thm.nprems_of @{thm D.ipE2});
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm LF.ipE2}, @{thm D.ipE2}));
val _ = \<^assert> (length (light_prems \<^context> @{thm LF.ipE2}) = 1);
(* the hand-written inversion lemma *)
val _ = \<^assert> (phi_equal (\<^const_name>\<open>LF\<close>, \<^const_name>\<open>D\<close>) (@{thm LF.ipE'}, @{thm D.ipE2}));
\<close>

end
