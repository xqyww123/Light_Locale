(* Plan section 7 test 6 (plan lines 4421-4424), the fixture of the [dest!] downstream row. *)
theory Base_Dest_Bang
  imports Light_Locale_Base
begin

consts Rc :: 'a  Sc :: 'a  Qc :: 'a
axiomatization where Sc_ax: "Sc x"

context D begin
lemma bad4d [dest!]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x" by auto
end

context LF begin
lemma bad4d [dest!]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> Qc a \<Longrightarrow> \<exists>x :: 'q. Qc x" by auto
end

end
