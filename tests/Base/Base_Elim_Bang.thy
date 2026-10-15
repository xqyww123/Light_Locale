(* Plan section 7 test 6 (plan lines 4424-4427), the fixture of the [elim!] downstream row: a global
   declaration, so its own theory in Light_Locale_Base, imported by exactly one leaf of
   Light_Locale_Test.  In the declaration block the same goal closes by auto on both sides: the
   block copy has the parameter S fixed and cannot match Rc a b, whereas a theory copy with a
   schematic ?S leaking into the block would consume Rc a b and leave the goal open, as it does
   downstream (Test6_Elim_Bang). *)
theory Base_Elim_Bang
  imports Light_Locale_Base
begin

consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context D begin
lemma bad4 [elim!]: "Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y" by auto
end

context LF begin
lemma bad4 [elim!]: "Rc x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y" by auto
end

end
