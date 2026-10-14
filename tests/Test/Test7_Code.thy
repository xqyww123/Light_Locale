(* Plan section 7 test 7: the two polarities of code equations (section 3.3's three branches).  In the predicate-free Setting a definition has a theory-level default code equation while the heavy twin's has none; a fun's constant has none outside the block (Code.declare_default_eqns is a pervasive = false declaration); inside the block value does not fail: the term has a free variable and goes to Nbe (value_command.ML:38-41), as in a heavy block.  In the gate fixture LF (with a predicate) a definition and a fun have none, as in the heavy twin, and a hand-written [code] gives stock's "Not an equation" warning. *)
theory Test7_Code
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
fun value_ok ctxt t = can (Value_Command.value ctxt) t;
fun value_error ctxt t = (Value_Command.value ctxt t; NONE) handle ERROR msg => SOME (XML.content_of (YXML.parse_body msg));
\<close>

light_locale Setting = fixes n :: nat
locale Setting0 = fixes n :: nat

context Setting begin
definition dcode :: nat where "dcode = n + 1"
fun ffun :: "nat \<Rightarrow> nat" where "ffun 0 = n" | "ffun (Suc k) = ffun k"
ML_val \<open>
val _ = \<^assert> (value_ok \<^context> \<^term>\<open>ffun 1\<close>);
\<close>
end

context Setting0 begin
definition dcode0 :: nat where "dcode0 = n + 1"
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (value_ok ctxt \<^term>\<open>Setting.dcode 3\<close>);
val _ = \<^assert> (Option.map (String.isPrefix "No code equations") (value_error ctxt \<^term>\<open>Setting.ffun 3 1\<close>) = SOME true);
val _ = \<^assert> (Option.map (String.isPrefix "No code equations") (value_error ctxt \<^term>\<open>Setting0.dcode0 3\<close>) = SOME true);
\<close>

context LF begin
definition dlf :: nat where "dlf = 1"
fun flf :: "nat \<Rightarrow> nat" where "flf 0 = 0" | "flf (Suc k) = flf k"
end

context D begin
definition dd :: nat where "dd = 1"
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*define abstracts only over the fixed variables of the right-hand side: dlf, flf and dd take no S*)
val _ = \<^assert> (Option.map (String.isPrefix "No code equations") (value_error ctxt \<^term>\<open>LF.dlf\<close>) = SOME true);
val _ = \<^assert> (Option.map (String.isPrefix "No code equations") (value_error ctxt \<^term>\<open>LF.flf 1\<close>) = SOME true);
val _ = \<^assert> (Option.map (String.isPrefix "No code equations") (value_error ctxt \<^term>\<open>D.dd\<close>) = SOME true);
val (_, w) = with_warnings (fn () => declare_in (Named_Target.theory_init \<^theory>) "LF.dlf_def" "[code]");
val _ = \<^assert> (exists (String.isPrefix "Not an equation") w);
\<close>

end
