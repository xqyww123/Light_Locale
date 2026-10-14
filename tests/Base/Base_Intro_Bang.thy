(* Plan section 7 test 6 (plan line 4747), the fixture of the [intro!] polarity twin: a global
   declaration, so its own theory in Light_Locale_Base, imported by exactly one leaf of
   Light_Locale_Test.  In the declaration block the rule closes Pc a ==> Sc a by auto on both
   sides. *)
theory Base_Intro_Bang
  imports Light_Locale_Base
begin

consts Pc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context D begin
lemma fooI [intro!]: "Pc x \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Pc (a :: 'q) \<Longrightarrow> Sc a" by auto
end

context LF begin
lemma fooI [intro!]: "Pc x \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma "Pc (a :: 'q) \<Longrightarrow> Sc a" by auto
end

end
