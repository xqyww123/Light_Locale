(* Plan section 7 test 1 (invariance), rows that need a light locale in the theory: a heavy
   <base>_axioms reached through standard full activation still carries neither [simp] nor [intro]
   when the theory also declares a light locale; and a locale declared directly through the old
   interface Locale.register_locale has a Plain _axioms note, which a light locale reaching it
   syntax-only does not install while the locale-command twin does (decision 7, R20 polarity). *)
theory Test1_Old_Interface
  imports Test_Support "HOL-Algebra.Ring"
begin

light_locale LFr = ring

context ring begin
ML_val \<open>
val _ = \<^assert> (not (Test_Support.by_simp \<^context> \<^prop>\<open>ring R\<close>));
val _ = \<^assert> (not (Test_Support.proves safe_tac \<^context> \<^prop>\<open>ring R\<close>));
\<close>
end

(* the old interface: one parameter, no predicate, one note named OldL_axioms *)
setup \<open>
  Locale.register_locale (Binding.name "OldL") ([], [(("z", \<^typ>\<open>nat\<close>), NoSyn)]) (NONE, [])
    (NONE, NONE) [] [] [] [("", [((Binding.name "OldL_axioms", []), [([@{thm TrueI}], [])])])] []
\<close>
light_locale LO = OldL
locale HO = OldL
context LO begin
ML_val \<open>\<^assert> (not (can (Proof_Context.get_thm \<^context>) "OldL_axioms"))\<close>
end
context HO begin
ML_val \<open>\<^assert> (can (Proof_Context.get_thm \<^context>) "OldL_axioms")\<close>
end

end
