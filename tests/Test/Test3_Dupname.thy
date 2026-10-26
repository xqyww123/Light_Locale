(* Plan section 7 test 3 (opening): a short name falls to the theory fact of the same name.  After
   the light block closes, its local copy is gone and the reopened block silently resolves the short
   name to the theory-level fact; in the heavy twin it is the block fact. *)
theory Test3_Dupname
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

axiomatization Pc :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and Qc :: "('a, 'b) ring_scheme \<Rightarrow> bool"
  where pc: "Pc x x" and qc: "Qc R"

lemma dupname: "Pc c c" by (rule pc)

context LF begin
lemma dupname: "Qc S" by (rule qc)
end

context D begin
lemma dupname: "Qc S" by (rule qc)
end

context LF begin
ML \<open>
  val _ = \<^assert> (dest_Const_name (Term.head_of (HOLogic.dest_Trueprop (Thm.prop_of @{thm dupname}))) =
    \<^const_name>\<open>Pc\<close>)\<close>
end

context D begin
ML \<open>val _ = \<^assert> (Thm.prop_of @{thm dupname} aconv @{prop "Qc S"})\<close>
end

end
