(* Plan section 7 test 6 (plan line 4714): the method modifier del: LF.bad in a block proof -- after
   declare LF.bad[dest] in the reopened block and the control (blast closes the goal),
   "blast del: LF.bad" does not. *)
theory Test6_Del_Method
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_blast = proves (fn c => blast_tac c 1);
\<close>

context LF begin
lemma bad: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

context LF begin
declare LF.bad[dest]
ML_val \<open>
val _ = \<^assert> (by_blast \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>);
val _ = \<^assert> (not (can (fn () => proof_after {apply = false} \<^context> [] "blast del: LF.bad" \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>) ()));
val _ = \<^assert> (can (fn () => proof_after {apply = false} \<^context> [] "blast" \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>) ());
\<close>
end

end
