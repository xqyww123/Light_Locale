(* Plan section 7 test 6 (plan line 4717): blast del: LF.fooE in a reopened block -- the control
   first (blast closes Pc c ==> Sc c, which only fooE closes), then blast del: LF.fooE does not;
   the same method text closes a goal that needs no rule, so a misread of the text cannot pass the
   negative row (plan line 3792). *)
theory Test6_Del_BlastDel
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
(* c is monomorphic: with a polymorphic c the two occurrences in Pc c ==> Sc c get different types *)
consts Pc :: 'a  Sc :: 'a  c :: nat
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooE [elim, consumes 1, case_names Hyp]: "Pc x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
end

context LF begin
ML \<open>local
val del = "blast del: LF.fooE";
val _ = \<^assert> (can (fn () => run \<^context> [] "blast" "Pc c \<Longrightarrow> Sc c") ());
val _ = \<^assert> (can (fn () => run \<^context> [] del "Pc c \<Longrightarrow> Pc c") ());
val _ = \<^assert> (not (can (fn () => run \<^context> [] del "Pc c \<Longrightarrow> Sc c") ()));
in end\<close>
end

end
