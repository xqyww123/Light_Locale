(* Plan section 7 test 6, a heavy locale importing a light one (plan lines 4740-4749; REV19-14,
   section 11 (39)): locale H = LF + fixes z assumes hz.  In H's block the bare lemmas foo2
   [case_names a b] = LF.foo keeps the K tag (the notes callback puts it back after
   thm_definition, whose inference rules clear every tag), so case a lands on A as in the heavy
   twin Hh's block; the bare declare LF.foo [elim] registers a rule whose major premise is A; the
   compensating spelling LF.foo[OF LF_axioms] is the bare copy with its exported premise
   discharged (K 0, as the twin); the block re-opened and the theory copies after interpretation
   I: H t 0 keep K through the activation morphisms; "using LF_axioms h proof cases" prints the
   twin's cases (pinned to ip's z / s), the bare "using h proof cases" falls to case_split, after
   the interpretation the same pair at theory level, the cases compared term by term with the
   twin's interpretation Ih (the instance names differ, LF.ip t against D.ip t: twin_names).  The
   notes callback is shared by every named target: a class block, a theory-level anonymous
   block and a heavy importer's header notes clause (H2; its theory copy H2.foo2 carries no K, as
   before) keep K alike.  The premise-count door: a global_interpretation inside context fixes
   ... assumes ... begin puts the block's assumption in front of every activated fact, so K is
   not put back (J.foo2); the door's reference is the normal form, so a K-tagged input not in
   HHF form keeps K on the local copy (foo_nhhf, reachable from ML only).  Pinned as it is,
   outside this fix: the copy a nested context assumes ... begin inside H's block leaves behind
   in H's block (foo3) -- K 0, the nested assumption first; milestone 3's narrow variant owns
   that path and must tag it K = count_of th + the added premises = 2.  The row of plan lines
   4748-4749 is dropped (section 11, item (27)). *)
theory Test6_Heavy_Imports
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"
axiomatization t :: "nat ring" where t: "cring t"

ML \<open>
val natT = \<^typ>\<open>nat\<close>;
fun major_light ctxt th = Light_Locale_Axiom_Facts.is_light_prop ctxt (Thm.major_prem_of th);
(*a light copy against its heavy twin: Rule_Cases equal up to K = 1, the own premises and the
  conclusion the twin's statement, the first own premise not the light predicate*)
fun light_copy ctxt (thl, thh) =
  diff_K 1 (thl, thh) andalso
  same_shape (Logic.list_implies (Exported_Premises.own_prems thl, Thm.concl_of thl), Thm.prop_of thh) andalso
  not (Light_Locale_Axiom_Facts.is_light_prop ctxt (hd (Exported_Premises.own_prems thl)));
(*a light elim registration against the twin's: K = 1 on the key, the derived rule's major
  premise is A as the twin's*)
fun light_elim ctxt ((key, plain), (hkey, hplain)) =
  Exported_Premises.count_of key = 1 andalso not (major_light ctxt plain) andalso
  same_shape (Thm.major_prem_of plain, Thm.major_prem_of hplain) andalso diff_K 1 (key, hkey);
\<close>

context D begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end
context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
inductive ip :: "nat \<Rightarrow> bool" where z: "ip 0" | s: "Pc S n \<Longrightarrow> ip n \<Longrightarrow> ip (Suc n)"
end

locale Hh = D + fixes z :: nat assumes hz: "Qc z"
context Hh begin
lemmas foo2 [case_names a b] = foo
declare foo [elim]
ML \<open>
val heavy_foo2 = @{thm foo2};
val heavy_foo_elim = claset_rule \<^context> Bires.elim_kind @{thm foo};
val heavy_H_cases =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "ip n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_text st end;
\<close>
end
interpretation Ih: Hh "UP t" t 0 by (rule Hh.intro) (rule D.intro, simp_all add: UP_cring_def t Hh_axioms_def Qc1_ax)
ML \<open>
val heavy_interp =
  let
    val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "D.ip t n";
    val st = run ctxt [h] "cases" "W n";
  in \<^assert> (case_names st = ["z", "s"]); cases_terms canonical_vars st end;
\<close>

locale H = LF + fixes z :: nat assumes hz: "Qc z"
context H begin
lemmas foo2 [case_names a b] = LF.foo
ML_val \<open>
(* (i) the bare lemmas: case a lands on A, consumes 1 = K *)
val (info, n) = Rule_Cases.get @{thm foo2};
val _ = \<^assert> (map (#1 o #1) info = ["a", "b"] andalso n = 1);
val _ = \<^assert> (light_copy \<^context> (@{thm foo2}, heavy_foo2));
\<close>
declare LF.foo [elim]
ML_val \<open>
(* (ii) the bare declare: the registered rule's major premise is A, as the twin's *)
val _ = \<^assert> (light_elim \<^context> (claset_rule \<^context> Bires.elim_kind @{thm LF.foo}, heavy_foo_elim));
\<close>
lemmas foo2' [case_names a b] = LF.foo[OF LF_axioms]
ML_val \<open>
(* the compensating spelling: the bare copy with its exported premise discharged, K 0 as the twin *)
val _ = \<^assert> (diff_K 0 (@{thm foo2'}, heavy_foo2));
val _ = \<^assert> (Thm.eq_thm_prop (Exported_Premises.discharge [@{thm LF_axioms}] @{thm foo2}, @{thm foo2'}));
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip S n";
val _ = \<^assert> (cases_text (run ctxt [@{thm LF_axioms}, h] "cases" "W n") = heavy_H_cases);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>
(* the nested layer, pinned as it is (outside this fix): K 0, the nested assumption first;
   milestone 3's target is K = count_of th + the added premises = 2 *)
context assumes hc: "Qc (0::nat)" begin
lemmas foo3 = LF.foo
end
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm foo3} = 0 andalso Thm.nprems_of @{thm foo3} = 4 andalso
  hd (Thm.prems_of @{thm foo3}) aconv \<^prop>\<open>Qc (0::nat)\<close>);
\<close>
end

context H begin
ML_val \<open>
(* (iii) the block re-opened (the identity morphism): as (i) and (ii) *)
val _ = \<^assert> (light_copy \<^context> (@{thm foo2}, heavy_foo2));
val _ = \<^assert> (light_elim \<^context> (claset_rule \<^context> Bires.elim_kind @{thm LF.foo}, heavy_foo_elim));
\<close>
end

interpretation I: H t 0 by (simp add: H_def H_axioms_def LF_def UP_cring_def t Qc1_ax)
ML_val \<open>
(* (iv) the theory copy of foo2 after the interpretation (the registration morphism) against
   the twin's; LF's foo has no interpreted copy (the exported theorem serves every context):
   its theory-level elim registration against the twin's interpreted copy *)
val ctxt = \<^context>;
val _ = \<^assert> (light_copy ctxt (@{thm I.foo2}, @{thm Ih.foo2}));
val _ = \<^assert> (light_elim ctxt
  (claset_rule ctxt Bires.elim_kind @{thm LF.foo}, claset_rule ctxt Bires.elim_kind @{thm Ih.foo}));
\<close>
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("n", natT)] "h" "LF.ip t n";
val st = run ctxt [@{thm I.LF_axioms}, h] "cases" "W n";
(* the ?case binds say ?P against the twin's ?Pa (D fixes P): up to renaming *)
val _ = \<^assert> (cases_terms (canonical_vars o twin_names ("LF", "D")) st = heavy_interp);
val _ = \<^assert> (case_names (run ctxt [h] "cases" "W n") = ["True", "False"]);
\<close>

(* the notes callback is shared by every named target: a class block, a theory-level anonymous
   block, a heavy importer's header notes clause (its theory copy carries no K, as before) *)
class Cz = fixes zc :: 'a assumes "zc = zc"
context Cz begin
lemmas foo2c [case_names a b] = LF.foo
ML_val \<open>\<^assert> (light_copy \<^context> (@{thm foo2c}, heavy_foo2))\<close>
end
context assumes hq: "Qc (1::nat)" begin
lemmas foo2t [case_names a b] = LF.foo
ML_val \<open>\<^assert> (light_copy \<^context> (@{thm foo2t}, heavy_foo2))\<close>
end
locale H2 = LF + fixes z :: nat assumes hz: "Qc z" notes foo2 [case_names a b] = LF.foo
context H2 begin
ML_val \<open>\<^assert> (light_copy \<^context> (@{thm foo2}, heavy_foo2))\<close>
end
ML_val \<open>\<^assert> (not (has_K_tag @{thm H2.foo2}))\<close>

(* the premise-count door: the block's assumption is put in front of every fact the
   global_interpretation activates, so K (which counts the leading premises) is not put back *)
context fixes x :: nat assumes hx: "Qc x" begin
global_interpretation J: H t x by (simp add: H_def H_axioms_def LF_def UP_cring_def t hx)
end
ML_val \<open>
val th = @{thm J.foo2};
val _ = \<^assert> (Exported_Premises.count_of th = 0 andalso Thm.nprems_of th = 4 andalso
  same_shape (hd (Thm.prems_of th), Logic.varify_global \<^prop>\<open>Qc (x::nat)\<close>));
\<close>

(* controls: no heavy theorem carries the K tag *)
ML_val \<open>
val _ = \<^assert> (not (has_K_tag heavy_foo2) andalso not (has_K_tag (#1 heavy_foo_elim)));
val _ = \<^assert> (not (has_K_tag @{thm Ih.foo2}) andalso not (has_K_tag @{thm H.foo2}));
\<close>

(* the premise-count door takes the normal form as its reference (section 11 (39) M7): a K-tagged
   input not in HHF form (the light predicate, then a meta-all over own premises: 1 premise, 3
   after Goal.norm_result) keeps K = 1 on the local copy; reachable only from ML, since the
   export morphism of lemmas and declare normalises a result not in HHF form, which clears every
   tag *)
context H begin
local_setup \<open>fn lthy =>
  let
    val th =
      Thm.forall_intr_vars @{thm conjI}
      |> Thm.implies_intr (Thm.cprop_of @{thm LF_axioms})
      |> Exported_Premises.put 1;
    val _ = \<^assert> (Thm.nprems_of th = 1 andalso Exported_Premises.count_of th = 1 andalso
      not (Drule.is_norm_hhf {protect = false} (Thm.prop_of th)));
  in Local_Theory.notes [((\<^binding>\<open>foo_nhhf\<close>, []), [([th], [])])] lthy |> snd end
\<close>
ML_val \<open>
val th = @{thm foo_nhhf};
val _ = \<^assert> (Thm.nprems_of th = 3 andalso hd (Thm.prems_of th) aconv Thm.prop_of @{thm LF_axioms});
val _ = \<^assert> (Exported_Premises.count_of th = 1);
\<close>
end

end
