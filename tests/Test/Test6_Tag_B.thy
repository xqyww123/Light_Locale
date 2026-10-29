(* Plan section 7 test 6, redeclaring a tagged theorem adds no premise, leaf B (plan lines
   4652, 4654-4656), with leaf A's fixture (fooNk: SetN.fooN with K 1 written by hand, see leaf
   A): lemmas fooN2 [dest] = fooNk in context LF keeps K 1 and the statement (no LF ?S); read after
   the block's end, the theory's claset has no rule with an LF ?S premise and the dest rule keyed
   by fooNk's proposition has major premise Qn ?n. *)
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

lemmas fooNk = SetN.fooN [setclass 1]

context LF begin
lemmas fooN2 [dest] = fooNk
end

(* after end: the open block's claset never sees theory-level registrations, so the reads are
   made at theory level (section 11, item (23)) *)
ML \<open>
val _ = \<^assert> (Setclass.count_of @{thm LF.fooN2} = 1 andalso Thm.eq_thm_prop (@{thm LF.fooN2}, @{thm SetN.fooN}));
val _ = \<^assert> (major_prem_is \<^context> "Qn (n :: nat)" (#2 (claset_rule \<^context> Bires.dest_kind @{thm LF.fooN2})));
val _ = \<^assert> (null (Classical.dest_decls \<^context> (fn (key, _) =>
  exists (Light_Locale_Axiom_Facts.is_light_prop \<^context>) (Thm.prems_of key))));
\<close>

end
