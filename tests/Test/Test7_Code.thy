(* Plan section 7 test 7 (plan lines 4829-4835): the two polarities of code equations (section
   3.3's three branches).  In the predicate-free Setting a definition has a theory-level default
   code equation while the heavy twin's has none; a fun's constant has none outside the block
   (Code.declare_default_eqns is a pervasive = false declaration) -- on both sides; inside the
   block value does not fail and returns the term unevaluated (it has a free variable and goes to
   Nbe, value_command.ML:38-41), as in the heavy block.  In the gate fixture LF (with a predicate)
   a definition and a fun have none, as in the heavy twin, and a hand-written [code] inside the
   block gives stock's "Not an equation" warning. *)
theory Test7_Code
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>
(*value fails with "No code equations" / inside a block: value does not fail and the term comes
  back with its head unevaluated*)
fun no_code ctxt t = fails_prefix "No code equations" (fn () => Value_Command.value ctxt t);
fun value_unevaluated ctxt t = Term.head_of (Value_Command.value ctxt t) = Term.head_of t;
\<close>

light_locale Setting = fixes n :: nat
locale Setting0 = fixes n :: nat

context Setting begin
definition dcode :: nat where "dcode = n + 1"
fun ffun :: "nat \<Rightarrow> nat" where "ffun 0 = n" | "ffun (Suc k) = ffun k"
ML \<open>val _ = \<^assert> (value_unevaluated \<^context> \<^term>\<open>ffun 1\<close>)\<close>
end

context Setting0 begin
definition dcode0 :: nat where "dcode0 = n + 1"
fun ffun0 :: "nat \<Rightarrow> nat" where "ffun0 0 = n" | "ffun0 (Suc k) = ffun0 k"
ML \<open>val _ = \<^assert> (value_unevaluated \<^context> \<^term>\<open>ffun0 1\<close>)\<close>
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val _ = \<^assert> (can (Value_Command.value ctxt) \<^term>\<open>Setting.dcode 3\<close>);
val _ = no_code ctxt \<^term>\<open>Setting.ffun 3 1\<close>;
val _ = no_code ctxt \<^term>\<open>Setting0.dcode0 3\<close>;
val _ = no_code ctxt \<^term>\<open>Setting0.ffun0 3 1\<close>;
\<close>

context LF begin
definition dlf :: nat where "dlf = 1"
fun flf :: "nat \<Rightarrow> nat" where "flf 0 = 0" | "flf (Suc k) = flf k"
(*the hand-written [code] on a conditional fact, inside the block: stock's warning*)
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "dlf_def" "[code]")
  in \<^assert> (exists (String.isPrefix "Not an equation") w); lthy' end\<close>
end

context D begin
definition dd :: nat where "dd = 1"
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
(*define abstracts only over the fixed variables of the right-hand side: dlf, flf and dd take no S*)
val _ = no_code ctxt \<^term>\<open>LF.dlf\<close>;
val _ = no_code ctxt \<^term>\<open>LF.flf 1\<close>;
val _ = no_code ctxt \<^term>\<open>D.dd\<close>;
\<close>

end
