(* Plan section 7 test 6 (plan line 4714): the method modifier del: LF.bad in a block proof -- after
   declare LF.bad[dest] in the reopened block and the control (blast closes the goal), "blast del:
   LF.bad" does not; the same method text closes a goal that needs no rule, so a misread of the
   text cannot pass the negative row (plan line 3792). *)
theory Test6_Del_Method
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma bad: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

context LF begin
declare LF.bad[dest]
ML_val \<open>
val del = "blast del: LF.bad";
val _ = \<^assert> (can (fn () => run \<^context> [] "blast" "Rc a S \<Longrightarrow> Sc a") ());
val _ = \<^assert> (can (fn () => run \<^context> [] del "Rc a S \<Longrightarrow> Rc a S") ());
val _ = \<^assert> (not (can (fn () => run \<^context> [] del "Rc a S \<Longrightarrow> Sc a") ()));
\<close>
end

end
