(* Plan section 7 test 6 (plan lines 4710-4712): in the declaration block, declare LF.bad[rule del]
   warns "Undeclared classical rule" (the block's pass finds no LF.bad in the block's claset) and
   auto still closes the goal through the local copy bad, while the theory's registration of
   LF.bad is gone; then declare bad [rule del] removes the local copy and the goal no longer
   closes -- the block's and the theory's claset each read once. *)
theory Test6_Del_Decl
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

ML \<open>
fun elim_entry ctxt th = exists (fn (_, _, kind) => Bires.kind_is_elim kind) (claset_entries ctxt th);
\<close>

context LF begin
lemma bad [elim]: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML \<open>
val _ = \<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>);
val _ = \<^assert> (elim_entry \<^context> @{thm bad} andalso elim_entry (thy_ctxt \<^context>) @{thm LF.bad});
\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LF.bad" "[rule del]")
  in \<^assert> (exists (String.isPrefix "Undeclared classical rule") w); lthy' end\<close>
ML \<open>
val _ = \<^assert> (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>);
val _ = \<^assert> (not (elim_entry (thy_ctxt \<^context>) @{thm LF.bad}));
\<close>
declare bad [rule del]
ML \<open>
val _ = \<^assert> (not (by_auto \<^context> \<^prop>\<open>Rc a S \<Longrightarrow> Sc a\<close>));
val _ = \<^assert> (not (elim_entry \<^context> @{thm bad}));
val _ = \<^assert> (not (elim_entry (thy_ctxt \<^context>) @{thm LF.bad}));
\<close>
end

end
