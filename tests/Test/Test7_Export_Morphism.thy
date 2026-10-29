(* Plan section 7 test 7 (plan lines 4848-4866; milestone 3's first item, second version): the
   theorem component of the declaration path to the background theory (section 3.3), observed
   through a thm-list Generic_Data filled by declaration (pervasive) inside the gate fixture's
   block.  A declaration is not a redeclaration, so every theorem goes the stock way -- the
   export puts LF ?S in front -- and K is counted layer by layer
   (ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md section 3.3): the light locale's layer adds one, a
   nested assumes layer pastes an ordinary premise (K 0 before the light locale's layer).  (a) A
   block lemma
   whose statement does not mention S (its local copy carries the hyp LF S) comes back as
   LF ?S ==> True, no hyps, count_of 1; in a nested context fixes y assumes "Qc y" it comes back as
   LF ?S ==> Qc ?y ==> True, count_of 1.  (b) LF.foo (K 1, no hyps) comes back as
   LF ?Sa ==> LF ?S ==> kx ?S = 0 with K 2 -- the same entry the stock syntax_declaration (d)
   makes of it: exactly two entries Thm.eq_thm_prop with the newest one, each K 2, no hyps.
   (c) The plain HOL fact X comes back as LF ?S ==> 0 + 0 = 0, count_of 1.  (c') Closed theorems
   with Rule_Cases tags through a bundle (a redeclaration): nat.induct keeps its cases and tags
   (count_of 0); fooc, a redeclaration the export does not change, is stored as itself, case names included.
   (c'') The theorem S == S of the block's fixed S (no hyps, not closed) comes back as
   LF ?S ==> ?S == ?S, count_of 1, no hyps.  The bundle rows: bundle b = LF.foo [keep] reads back
   as exactly one entry (LF.foo, count_of 1, a non-empty source list); bundle b0 = LF.foo reads
   back [] -- a record row, as in stock (Attrib.partial_evaluation drops entries without
   attributes before any light code runs).  (d) syntax_declaration (pervasive) of LF.foo gives the
   stock export shape, one premise more and count_of 2 (the newest entry of the table).  (e) The
   theory fact tg (K 1, one premise, no light predicate premise, no hyps) comes back as
   LF ?S ==> PROP ?A ==> PROP ?A, count_of 2, no hyps.  (f) A theorem with hyps and K 1 (made by
   implies_intr on LF_axioms and put) comes back as LF ?S ==> Qc 0 ==> LF ?S with K 2.  No interpretation of LF in this leaf. *)
theory Test7_Export_Morphism
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>structure Thm_Data = Generic_Data (type T = thm list val empty = [] val merge = Thm.merge_thms)\<close>

consts Qc :: "nat \<Rightarrow> bool"  kx :: "('a, 'b) ring_scheme \<Rightarrow> nat"
axiomatization where kx_ax: "kx R = 0"
lemma X: "(0::nat) + 0 = 0" by simp
lemma tg [setclass 1]: "PROP A \<Longrightarrow> PROP A" .
lemma fooc [case_names x]: "LF S \<Longrightarrow> P \<Longrightarrow> P" by assumption

context LF begin
lemma foo: "kx S = 0" by (rule kx_ax)
lemma t7: True by simp
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm t7}]))\<close>
context fixes y :: nat assumes "Qc y" begin
lemma t8: True by simp
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm t8}]))\<close>
end
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm LF.foo}, @{thm X}]))\<close>
(* (c'') *)
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [Thm.reflexive @{cterm S}]))\<close>
(* (c') and the bundle rows *)
bundle b2 = nat.induct [keep] fooc [keep]
bundle b = LF.foo [keep]
bundle b0 = LF.foo
end

context LF begin
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm tg}]))\<close>
(* (f): LF_axioms carries the hyp LF S in the block; one premise in front and K 1 written by hand *)
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi
  [Setclass.put 1 (Thm.implies_intr \<^cprop>\<open>Qc 0\<close> @{thm LF_axioms})]))\<close>
syntax_declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm LF.foo}]))\<close>
end

(* the bindings of the rows (an ML command stops the theory on failure, so it binds only what
   cannot fail); each row is an ML command of its own, the first failing one ends the theory *)
ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val table = Thm_Data.get (Context.Theory \<^theory>);
fun find p = (case filter p table of [th] => th | ths => error ("entries: " ^ string_of_int (length ths)));
fun clean th = null (Thm.hyps_of th);
fun entry name th =
  (case filter (fn ([th'], _) => Thm.eq_thm_prop (th', th) | _ => false) (bundle_of ctxt name) of
    [([th'], _)] => th'
  | _ => error ("bundle entry of " ^ name));
(* (d) the newest entry (append puts the new facts in front), the stock export shape *)
val d = hd table;
\<close>
(* (a) *)
ML \<open>local
val a1 = find (fn th => Thm.prop_of th aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> True\<close>);
val _ = \<^assert> (clean a1 andalso Setclass.count_of a1 = 1);
val a2 = find (fn th => Thm.prop_of th aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc y \<Longrightarrow> True\<close>);
val _ = \<^assert> (clean a2 andalso Setclass.count_of a2 = 1);
in end\<close>
(* (c'') *)
ML \<open>local
val c2 = find (fn th => Thm.prop_of th aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (S :: ('a, 'b) ring_scheme) \<equiv> S\<close>);
val _ = \<^assert> (clean c2 andalso Setclass.count_of c2 = 1);
in end\<close>
(* (c'): nat.induct keeps its cases and tags *)
ML \<open>local
val _ = \<^assert> (length (bundle_of ctxt "LF.b2") = 2);
val ni = entry "LF.b2" @{thm nat.induct};
val _ = \<^assert> (Rule_Cases.get ni = Rule_Cases.get @{thm nat.induct} andalso
  Thm.get_tags ni = Thm.get_tags @{thm nat.induct} andalso Setclass.count_of ni = 0);
in end\<close>
(* (c'): fooc is stored as itself, its case_names tag with it *)
ML \<open>local
val _ = \<^assert> (is_some (AList.lookup (op =) (Thm.get_tags @{thm fooc}) "case_names"));
val _ = \<^assert> (not (null (#1 (Rule_Cases.get @{thm fooc}))));
val fc = entry "LF.b2" @{thm fooc};
val _ = \<^assert> (Setclass.count_of fc = 0 andalso Rule_Cases.get fc = Rule_Cases.get @{thm fooc});
in end\<close>
(* the bundle rows *)
ML \<open>
val _ = \<^assert>
  (case bundle_of ctxt "LF.b" of
    [([th], srcs)] => Thm.eq_thm_prop (th, @{thm LF.foo}) andalso Setclass.count_of th = 1 andalso not (null srcs)
  | _ => false);
(*record only (plan line 4866): the attribute-less bundle is empty, as in stock*)
val _ = \<^assert> (null (bundle_of ctxt "LF.b0"));
val _ = \<^assert> (not (Thm.eq_thm_prop (d, @{thm LF.foo})));
\<close>
(* (d) *)
ML \<open>val _ = \<^assert> (Thm.nprems_of d = Thm.nprems_of @{thm LF.foo} + 1 andalso Setclass.count_of d = 2 andalso clean d)\<close>
(* (b) the unflagged declaration and the stock syntax_declaration (d) give the same result on the
   same input: exactly two entries Thm.eq_thm_prop with the newest one, each K 2 and no hyps
   (the statement LF ?Sa ==> LF ?S ==> kx ?S = 0 is not written down: zero_var_indexes names the
   clashing variable and the block's type variables differ per entry) *)
ML \<open>local
val bs = filter (fn th => Thm.eq_thm_prop (th, d)) table;
val _ = \<^assert> (length bs = 2 andalso
  forall (fn th => Setclass.count_of th = 2 andalso clean th) bs);
in end\<close>
(* (c) *)
ML \<open>local
val c = find (fn th => same_shape (Thm.prop_of th, Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (0::nat) + 0 = 0\<close>));
val _ = \<^assert> (Setclass.count_of c = 1 andalso clean c);
in end\<close>
(* (e) *)
ML \<open>local
val e = find (fn th => same_shape (Thm.prop_of th, Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> PROP A \<Longrightarrow> PROP A\<close>));
val _ = \<^assert> (Thm.nprems_of e = 2 andalso Setclass.count_of e = 2 andalso clean e);
in end\<close>
(* (f) *)
ML \<open>local
val f = find (fn th => same_shape (Thm.prop_of th, Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc 0 \<Longrightarrow> LF S\<close>));
val _ = \<^assert> (Thm.nprems_of f = 2 andalso Setclass.count_of f = 2 andalso clean f);
in end\<close>

end
