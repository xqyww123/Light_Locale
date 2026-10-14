(* Plan section 7 test 7: the alignment rows of the whole-table evaluation and the split-back
   (section 3.4): (a) an unnamed lemma [simp, OF h] goes through the temporary binding, the split
   and the regrouping and gives exactly one result; (b) a direct Local_Theory.notes with three
   inputs -- unnamed without attributes, unnamed [simp, OF hc] (split into a declaration entry and
   the fact), named with a rule attribute reading an earlier fact -- returns three results with the
   inputs' names and theorems; (c) a block definition exercises the unnamed note inside define. *)
theory Test7_Alignment
  imports Test_Support
begin

consts cc :: 'b  f1 :: "'a \<Rightarrow> 'a"  f2 :: "'a \<Rightarrow> 'a"  f3 :: "'a \<Rightarrow> 'a"

light_locale LH = fixes h :: "'a \<Rightarrow> 'b" assumes hc: "\<And>x. h x = cc"
begin

(* (a) *)
lemma [simp, OF hc]: "h (f1 x) = cc \<Longrightarrow> h (f1 x) = cc" by simp

(* (b) *)
local_setup \<open>fn lthy =>
  let
    val thA = @{thm hc} RS @{thm sym};
    val thB = @{lemma "h (f2 x) = cc \<Longrightarrow> h (f2 x) = cc" by simp};
    val thC = @{lemma "h (f3 x) = cc \<Longrightarrow> h (f3 x) = cc" by simp};
    val simp_src = Attrib.check_src lthy (Token.make_src ("simp", Position.none) []);
    fun of_src name =
      Attrib.check_src lthy (Token.make_src ("OF", Position.none) [Token.make_string (name, Position.none)]);
    val (results, lthy') = Local_Theory.notes
      [((Binding.empty, []), [([thA], [])]),
       ((Binding.empty, []), [([thB], [simp_src, of_src "hc"])]),
       ((Binding.name "c3", []), [([thC], [of_src "hc"])])] lthy;
    val _ = \<^assert> (map #1 results = ["", "", "local.c3"]);
    (*the local copies: h stays the block's fixed variable, x becomes schematic*)
    fun sx t = Term.map_aterms (fn Free ("x", T) => Var (("x", 0), T) | u => u) t;
    val _ = \<^assert> (eq_list (eq_list (op aconv)) (map (map Thm.prop_of o #2) results,
      [[sx \<^prop>\<open>cc = h (x::'a)\<close>], [sx \<^prop>\<open>h (f2 (x::'a)) = cc\<close>], [sx \<^prop>\<open>h (f3 (x::'a)) = cc\<close>]]));
    val _ = \<^assert> (forall (fn (_, ths) => forall (fn th => Exported_Premises.count_of th = 0) ths) results);
  in lthy' end\<close>

(* (c) *)
definition dq where "dq = cc"
ML_val \<open>
val _ = \<^assert> (XML.content_of (YXML.parse_body (Thm.string_of_thm \<^context> @{thm dq_def})) = "dq = cc");
val _ = \<^assert> (Exported_Premises.count_of @{thm dq_def} = 0);
\<close>

end

ML \<open>
val _ = \<^assert> (Exported_Premises.count_of @{thm LH.dq_def} = 1);
val _ = \<^assert> (Exported_Premises.count_of @{thm LH.c3} = 1);
val _ = \<^assert> (Thm.nprems_of @{thm LH.c3} = 1);
\<close>

end
