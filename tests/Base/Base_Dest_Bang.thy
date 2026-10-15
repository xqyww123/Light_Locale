(* Plan section 7 test 6 (plan lines 4424-4427), the fixture of the [dest!] downstream row; the
   in-block goal as in Base_Elim_Bang. *)
theory Base_Dest_Bang
  imports Light_Locale_Base
begin

consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context D begin
lemma bad4d [dest!]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y" by auto
end

context LF begin
lemma bad4d [dest!]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Rc (a :: 'q) (b :: ('z, 'w) ring_scheme) \<Longrightarrow> \<exists>y :: ('z, 'w) ring_scheme. Rc a y" by auto
end

end
