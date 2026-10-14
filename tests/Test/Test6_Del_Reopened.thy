(* Plan section 7 test 6 (plan lines 4713-4714): in the reopened block, declare LF.bad[dest], the
   positive control (blast closes the goal; the theory's claset has a dest-kind entry keyed by
   LF.bad's proposition), declare LF.bad[rule del], blast no longer closes it and the block's
   claset has no such dest entry; after end the theory's claset has none either. *)
theory Test6_Del_Reopened
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

ML \<open>
val thy_ctxt = Proof_Context.init_global o Proof_Context.theory_of;
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val by_blast = proves (fn c => blast_tac c 1);
fun dest_entry ctxt th = exists (fn (_, _, kind) => kind = Bires.dest_kind) (claset_entries ctxt th);
\<close>

context LF begin
lemma bad: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

context LF begin
declare LF.bad[dest]
ML_val \<open>
val _ = \<^assert> (by_blast \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>);
val _ = \<^assert> (dest_entry (thy_ctxt \<^context>) @{thm LF.bad});
\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.bad" "[rule del]")
  in \<^assert> (null w); lthy' end\<close>
ML_val \<open>
val _ = \<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>));
val _ = \<^assert> (not (dest_entry \<^context> @{thm LF.bad}));
\<close>
end

ML \<open>val _ = \<^assert> (not (dest_entry \<^context> @{thm LF.bad}));\<close>

end
