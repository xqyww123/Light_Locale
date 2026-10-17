(* Plan section 7 test 9 (structure): with_implicit_structure (plan section 4 item 7; rows at
   plan 5303-5308 and 5254-5257): block scope inside a proof -- the value holds for the rest of
   the proof block, a subproof inherits it and its own value ends with it; prove mode and chain
   mode; the placeholder fixed for the first time inside a proof, outside body mode. *)
theory Test9_With
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;
val int_rec = "\<lparr>carrier = UNIV, mult = (+), one = (0 :: int)\<rparr>";
val nat_rec = "\<lparr>carrier = UNIV, mult = (+), one = (0 :: nat)\<rparr>";
fun bare_on ctxt text = \<^assert> (bare_denotes ctxt text);
val placeholder_fixed = \<^assert> o Test_Support.placeholder_fixed;
\<close>


subsection \<open>State mode: the proof block, a subproof, back (plan 5303-5304)\<close>

context LF
begin

lemma "x \<otimes> y = x \<otimes> y"
proof -
  with_implicit_structure "S"
  ML_prf \<open>bare_on \<^context> "S"\<close>
  have True
  proof -
    ML_prf \<open>bare_on \<^context> "S"\<close>
    with_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
    ML_prf \<open>bare_on \<^context> int_rec\<close>
    show True ..
  qed
  ML_prf \<open>bare_on \<^context> "S"\<close>
  show ?thesis ..
qed

ML_val \<open>\<^assert> (implicit_is \<^context> (reads \<^context> "UP S"))\<close>

end


subsection \<open>Prove mode and chain mode (plan 5305-5308)\<close>

lemma
  fixes S :: "('a, 'b) ring_scheme"
  assumes h: "cring S"
  shows "x \<otimes>\<^bsub>UP S\<^esub> y = x \<otimes>\<^bsub>UP S\<^esub> y"
  with_implicit_structure "UP S"
  ML_prf \<open>bare_on \<^context> "UP S"\<close>
  apply (subgoal_tac "\<one> = \<one>\<^bsub>UP S\<^esub>")
  apply (rule refl)
  ML_prf \<open>bare_on \<^context> "UP S"\<close>
  apply (subgoal_tac "\<one> = \<one>\<^bsub>UP S\<^esub>")
  apply (rule refl)+
  done

lemma
  fixes S :: "('a, 'b) ring_scheme"
  assumes h: "cring S"
  shows "x \<otimes>\<^bsub>UP S\<^esub> y = x \<otimes>\<^bsub>UP S\<^esub> y"
proof -
  from h with_implicit_structure "UP S" have "cring S" .
  ML_prf \<open>bare_on \<^context> "UP S"\<close>
  show ?thesis ..
qed


subsection \<open>The first fix inside a proof (plan 5254-5257)\<close>

lemma "True"
proof -
  with_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
  with_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: nat monoid"
  ML_prf \<open>
    val ctxt = \<^context>;
    val _ = bare_on ctxt nat_rec;
    val _ = \<^assert> (not (has_placeholder (Syntax.read_prop ctxt "a \<otimes> b = a \<otimes> b")));
    val _ = placeholder_fixed ctxt;
  \<close>
  show True ..
qed

context D
begin
lemma "True"
proof -
  with_implicit_structure "S"
  with_implicit_structure "UP S"
  ML_prf \<open>
    val ctxt = \<^context>;
    val _ = bare_on ctxt "UP S";
    val _ = \<^assert> (not (has_placeholder (Syntax.read_prop ctxt "a \<otimes> b = a \<otimes> b")));
    val _ = placeholder_fixed ctxt;
  \<close>
  show True ..
qed
end

lemma "True"
proof -
  have True
  proof -
    with_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid"
    with_implicit_structure "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: nat monoid"
    ML_prf \<open>
      val ctxt = \<^context>;
      val _ = bare_on ctxt nat_rec;
      val _ = placeholder_fixed ctxt;
    \<close>
    show True ..
  qed
  show True ..
qed

end
