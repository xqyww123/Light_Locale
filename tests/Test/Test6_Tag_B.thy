(* Plan section 7 test 6, redeclaring a tagged theorem adds no premise, leaf B (plan lines
   4652, 4654-4656): lemmas fooN2 [dest] = SetN.fooN in context LF keeps K 1 and the statement
   (no LF ?S), the block's claset has no rule with an LF ?S premise, and at theory level the dest
   rule keyed by SetN.fooN's proposition has major premise Qn ?n. *)
theory Test6_Tag_B
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Qn :: "nat \<Rightarrow> bool"  Rn :: "nat \<Rightarrow> bool"  Rn' :: "nat \<Rightarrow> bool"
axiomatization where qr: "0 < n \<Longrightarrow> Qn n \<Longrightarrow> Rn n \<and> Rn' n"

light_locale SetN = fixes n :: nat
context SetN begin
context assumes hn: "0 < n" begin
lemma fooN: "Qn n \<Longrightarrow> Rn n \<and> Rn' n" by (rule qr[OF hn])
end
end

ML \<open>
fun major_is c th =
  (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of th)) of
    (Const (c', _), args) => c' = c andalso forall is_Var args
  | _ => false);
\<close>

context LF begin
lemmas fooN2 [dest] = SetN.fooN
ML_val \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LF.fooN2} = 1 andalso Thm.eq_thm_prop (@{thm LF.fooN2}, @{thm SetN.fooN}));
val _ = \<^assert> (not (exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of @{thm LF.fooN2})));
val _ = \<^assert> (null (Classical.dest_decls \<^context> (fn (key, _) =>
  exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of key))));
\<close>
end

ML \<open>
val _ = \<^assert> (exists (fn (_, plain, _) => major_is \<^const_name>\<open>Qn\<close> plain) (claset_entries \<^context> @{thm SetN.fooN}));
\<close>

end
