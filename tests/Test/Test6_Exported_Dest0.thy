(* Plan section 7 test 6 (plan lines 4626-4628), the control: at theory level declare LF.fooD0 [dest]
   without [exported_premises 0] registers a derived rule whose major premise is Rc ?x ?S. *)
theory Test6_Exported_Dest0
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Rc :: 'a  Sc :: 'a
axiomatization where Sc_ax: "Sc x"

context LF begin
lemma fooD0: "Rc x S \<Longrightarrow> Sc x" by (rule Sc_ax)
end

declare LF.fooD0 [dest]

ML \<open>
val _ = \<^assert> (exists (fn (_, plain, _) =>
    (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.major_prem_of plain)) of
      (Const (c, _), [Var _, Var _]) => c = \<^const_name>\<open>Rc\<close> | _ => false))
  (claset_entries \<^context> @{thm LF.fooD0}));
\<close>

end
