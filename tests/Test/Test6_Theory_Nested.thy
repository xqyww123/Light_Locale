(* Plan section 7 test 6, the theory-level nested blocks of milestone 3's first item (plan lines
   4740-4749; section 11 (40)).  A theory-level context assumes ... begin block is a theory
   target: the copies a lemma leaves in the enclosing layers come from standard_notes (the outer
   copies), and the block reads its own layer's copy after each command.  t4 under two assumes
   layers: K = 1 + 1 between the two ends, K 3 on the theory copy (second version: the theory
   copy keeps K through its morphism too); h3's row at theory level: the attribute's K on a
   lemma line survives the renumbering of the own layer's copy.  The usage hint (plan line
   882): a lemma line's attribute is applied once more on the theory copy, so [exported_premises
   1] on a lemma line in an assumes block gives the theory copy the absolute value 1 (fa); the
   lemmas spelling on the next line gives the block K 1 and the theory copy K 2 (fb; lemmas
   evaluates the static attribute before the notes, the export adds the layer's premise); a
   fixes-only block is not affected (fc).  Second version rows: r3 under an assumes layer and a
   defines layer (N3: the defines layer adds nothing, the outer copy K 1, the theory copy K 2);
   the bundle bt defined under an assumes layer (N19: its entry K 2); N8's theory-level half: a
   theory-level assumes layer whose only assumption is a sort constraint adds nothing to the
   theory copy's K (r8, r8t), a layer with Qc c beside it adds one (r8m) -- H's copies are in
   Test6_Heavy_Imports. *)
theory Test6_Theory_Nested
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"

context LF begin
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
end

(* two theory-level assumes layers *)
context assumes c1: "Qc (1::nat)" begin
context assumes c2: "Qc (2::nat)" begin
lemmas t4 = LF.foo
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm t4} = 2 andalso Thm.nprems_of @{thm t4} = 4 andalso
  hd (Thm.prems_of @{thm t4}) aconv \<^prop>\<open>Qc (2::nat)\<close>)\<close>
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm t4} = 3 andalso Thm.nprems_of @{thm t4} = 5)\<close>

(* h3's row at theory level, read from the own layer's copy; the usage hint.  h3, fa and fb are
   mechanism fixtures, not user scenarios (a hand-written K on a lemma line has no meaning) *)
context assumes c3: "Qc (3::nat)" begin
lemma h0: "Qc (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat)" for y by assumption
ML_val \<open>\<^assert> (Thm.maxidx_of @{thm h0[THEN conjunct1]} > 0)\<close>
lemma h3 [THEN conjunct1, exported_premises 1]: "Qc (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat) \<Longrightarrow> Pc y (3::nat) \<and> Pc y (3::nat)" for y by assumption
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm h3} = 1 andalso Thm.nprems_of @{thm h3} = 2)\<close>
lemma fa [exported_premises 1]: "Qc (3::nat) \<Longrightarrow> Qc (3::nat)" by assumption
lemmas fb [exported_premises 1] = fa
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fb} = 1 andalso Thm.nprems_of @{thm fb} = 1)\<close>
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fa} = 1 andalso Thm.nprems_of @{thm fa} = 2)\<close>
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fb} = 2 andalso Thm.nprems_of @{thm fb} = 2)\<close>
context fixes v :: nat begin
lemma fc [exported_premises 1]: "Qc v \<Longrightarrow> Qc v" by assumption
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm fc} = 1 andalso Thm.nprems_of @{thm fc} = 1)\<close>

(* N3: an assumes layer over a defines layer.  The defines layer adds nothing (its equation is
   unfolded, c does not occur), the outer layer one: the outer copy K 1, the theory copy K 2 --
   made by an export with a fixed variable to generalise, which rebuilds the theorem *)
context assumes hq3: "Qc (0::nat)" begin
context fixes c :: nat defines c_def: "c \<equiv> (0::nat)" begin
lemmas r3 = LF.foo
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm r3} = 1 andalso Thm.nprems_of @{thm r3} = 3)\<close>
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm r3} = 2 andalso Thm.nprems_of @{thm r3} = 4 andalso
  hd (Thm.prems_of @{thm r3}) aconv \<^prop>\<open>Qc (0::nat)\<close>)\<close>

(* N19: the bundle path outside a light block keeps K plus the premises put in front: bt's entry
   is Qc 1 ==> LF ?S ==> A ==> B ==> A & B with K 2 ([keep]: an entry without an attribute source
   is dropped, attrib.ML:397) *)
context assumes c19: "Qc (1::nat)" begin
bundle bt = LF.foo [keep]
end
ML_val \<open>
val _ = \<^assert>
  (case bundle_of \<^context> "bt" of
    [([th], _)] =>
      Exported_Premises.count_of th = 2 andalso Thm.nprems_of th = 4 andalso
      hd (Thm.prems_of th) aconv \<^prop>\<open>Qc (1::nat)\<close>
  | _ => false);
\<close>

(* N8's theory-level half: the export puts PROP SORT_CONSTRAINT('a) in front and the normalisation
   deletes it again, so the layer adds nothing to the theory copy's K; with Qc c beside it the
   layer adds one.  One row per copy, read after the block's end. *)
context LF begin
lemma fooT: "Pc S (0::nat)" by (rule Pc_ax)
end
context assumes "SORT_CONSTRAINT('a::type)" begin
lemmas r8 = LF.foo
lemmas r8t = LF.fooT
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm r8} = 1 andalso Thm.nprems_of @{thm r8} = 3)\<close>
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm r8t} = 1 andalso Thm.nprems_of @{thm r8t} = 1)\<close>
context fixes c :: nat assumes hc8: "Qc c" "SORT_CONSTRAINT('a::type)" begin
lemmas r8m = LF.foo
end
ML_val \<open>\<^assert> (Exported_Premises.count_of @{thm r8m} = 2 andalso Thm.nprems_of @{thm r8m} = 4 andalso
  same_shape (hd (Thm.prems_of @{thm r8m}), Logic.varify_global \<^prop>\<open>Qc (c :: nat)\<close>))\<close>

end
