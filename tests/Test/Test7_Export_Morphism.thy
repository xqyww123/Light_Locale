(* Plan section 7 test 7 (plan lines 4848-4866): the theorem component of light_export_morphism
   (the declaration path to the background theory, section 3.3), observed through a thm-list
   Generic_Data filled by declaration (pervasive) inside the gate fixture's block.  (a) A block
   lemma whose statement does not mention S (its local copy carries the hyp LF S) comes back as
   LF ?S ==> True, no hyps, count_of 1; in a nested context fixes y assumes "Qc y" it comes back as
   LF ?S ==> Qc ?y ==> True, count_of 2.  (b) LF.foo comes back Thm.eq_thm_prop with the stored
   LF.foo, same nprems, count_of 1.  (c) A plain HOL fact X comes back as itself, count_of 0, tags
   unchanged.  (c') Closed theorems with Rule_Cases tags through a bundle: nat.induct keeps its
   cases and tags (count_of 0), the strict-form fooc (LF ?S ==> ?P ==> ?P with case names) comes
   back with count_of 0 and without its case names -- the two pin the branch order.  (c'') The
   theorem S == S of the block's fixed S (no hyps, not closed, not in exported form) comes back as
   LF ?S ==> ?S == ?S, count_of 1, no hyps (the stock branch; an implementation returning hyp-free
   theorems unchanged would store the block's Free).  The bundle rows: bundle b = LF.foo [keep]
   reads back as exactly one entry (LF.foo, count_of 1, a non-empty source list); bundle b0 =
   LF.foo reads back [] -- a record row, as in stock (Attrib.partial_evaluation drops entries
   without attributes before any light code runs).  (d) syntax_declaration (pervasive) of LF.foo
   gives the stock export shape, one premise more and count_of 0 (the newest entry of the table).
   (e) A theory fact tg that only carries the tag (one premise, no light predicate premise, no
   hyps) comes back with its statement unchanged, count_of 1, no hyps.  No interpretation of LF in
   this leaf. *)
theory Test7_Export_Morphism
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>structure Thm_Data = Generic_Data (type T = thm list val empty = [] val merge = Thm.merge_thms)\<close>

consts Qc :: "nat \<Rightarrow> bool"  kx :: "('a, 'b) ring_scheme \<Rightarrow> nat"
axiomatization where kx_ax: "kx R = 0"
lemma X: "(0::nat) + 0 = 0" by simp
lemma tg [exported_premises 1]: "PROP A \<Longrightarrow> PROP A" .
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
syntax_declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm LF.foo}]))\<close>
end

ML \<open>
val ctxt = Proof_Context.init_global \<^theory>;
val table = Thm_Data.get (Context.Theory \<^theory>);
fun find p = (case filter p table of [th] => th | ths => error ("entries: " ^ string_of_int (length ths)));
fun clean th = null (Thm.hyps_of th);
(* (a) *)
val a1 = find (fn th => Thm.prop_of th aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> True\<close>);
val _ = \<^assert> (clean a1 andalso Exported_Premises.count_of a1 = 1);
val a2 = find (fn th => Thm.prop_of th aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> Qc y \<Longrightarrow> True\<close>);
val _ = \<^assert> (clean a2 andalso Exported_Premises.count_of a2 = 2);
(* (b) *)
val b = find (fn th => Thm.eq_thm_prop (th, @{thm LF.foo}));
val _ = \<^assert> (Thm.nprems_of b = Thm.nprems_of @{thm LF.foo} andalso Exported_Premises.count_of b = 1);
(* (c) *)
val c = find (fn th => Thm.eq_thm_prop (th, @{thm X}));
val _ = \<^assert> (Exported_Premises.count_of c = 0 andalso Thm.get_tags c = Thm.get_tags @{thm X});
(* (c'') *)
val c2 = find (fn th => Thm.prop_of th aconv
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (S :: ('a, 'b) ring_scheme) \<equiv> S\<close>);
val _ = \<^assert> (clean c2 andalso Exported_Premises.count_of c2 = 1);
(* (c') *)
fun entry name th =
  (case filter (fn ([th'], _) => Thm.eq_thm_prop (th', th) | _ => false) (bundle_of ctxt name) of
    [([th'], _)] => th'
  | _ => error ("bundle entry of " ^ name));
val b2 = bundle_of ctxt "LF.b2";
val _ = \<^assert> (length b2 = 2);
val ni = entry "LF.b2" @{thm nat.induct};
val _ = \<^assert> (Rule_Cases.get ni = Rule_Cases.get @{thm nat.induct} andalso
  Thm.get_tags ni = Thm.get_tags @{thm nat.induct} andalso Exported_Premises.count_of ni = 0);
val fc = entry "LF.b2" @{thm fooc};
(*the strict form went through light_export: count_of 0 and the case_names tag dropped (decision
  9 (iii); Rule_Cases.get then only numbers the premises), where fooc itself carries it*)
val case_names_tag = AList.lookup (op =) (Thm.get_tags fc) "case_names";
val _ = \<^assert> (Exported_Premises.count_of fc = 0 andalso is_none case_names_tag);
val _ = \<^assert> (is_some (AList.lookup (op =) (Thm.get_tags @{thm fooc}) "case_names"));
val _ = \<^assert> (not (null (#1 (Rule_Cases.get @{thm fooc}))));
(* the bundle rows *)
val _ = \<^assert>
  (case bundle_of ctxt "LF.b" of
    [([th], srcs)] => Thm.eq_thm_prop (th, @{thm LF.foo}) andalso Exported_Premises.count_of th = 1 andalso not (null srcs)
  | _ => false);
(*record only (plan line 4866): the attribute-less bundle is empty, as in stock*)
val _ = \<^assert> (null (bundle_of ctxt "LF.b0"));
(* (e) *)
val e = find (fn th => Thm.eq_thm_prop (th, @{thm tg}));
val _ = \<^assert> (Thm.nprems_of e = 1 andalso Exported_Premises.count_of e = 1 andalso clean e);
(* (d) the newest entry (append puts the new facts in front), the stock export shape *)
val d = hd table;
val _ = \<^assert> (Thm.nprems_of d = Thm.nprems_of @{thm LF.foo} + 1 andalso Exported_Premises.count_of d = 0);
val _ = \<^assert> (not (Thm.eq_thm_prop (d, @{thm LF.foo})));
\<close>

end
