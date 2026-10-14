(* Plan section 7 test 6 (plan lines 4421-4424), the fixture of the [elim!] downstream row: a global
   declaration, so its own theory in Light_Locale_Base, imported by exactly one leaf of
   Light_Locale_Test.  In the declaration block the goal with Rc a b among its assumptions closes
   by auto on both sides (the block copies are ordinary safe rules). *)
theory Base_Elim_Bang
  imports Light_Locale_Base
begin

consts Rc :: 'a  Sc :: 'a  Qc :: 'a
axiomatization where Sc_ax: "Sc x"

context D begin
lemma bad4 [elim!]: "Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x" by auto
end

context LF begin
lemma bad4 [elim!]: "Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x" by auto
end

end
