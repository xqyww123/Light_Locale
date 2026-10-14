(* Plan section 7 test 7: the theorem component of light_export_morphism (the declaration path to the background theory, section 3.3), observed through a thm-list Generic_Data filled by declaration (pervasive) inside the gate fixture's block.  (a) A block lemma whose statement does not mention S (its local copy carries the hyp LF S) comes back as LF ?S ==> True, no hyps, count_of 1; in a nested context fixes y assumes "Qc y" it comes back as LF ?S ==> Qc ?y ==> True, count_of 2.  (b) LF.foo comes back Thm.eq_thm_prop with the stored LF.foo, same nprems, count_of 1.  (c) A plain HOL fact X comes back as itself, count_of 0, tags unchanged.  (d) A theory fact tg that only carries the tag (one premise, no light predicate premise, no hyps) comes back with its statement unchanged, count_of 1, no hyps.  (e) syntax_declaration (pervasive) of LF.foo gives the stock export shape, one premise more and count_of 0.  No interpretation of LF in this leaf. *)
theory Test7_Export_Morphism
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>structure Thm_Data = Generic_Data (type T = thm list val empty = [] val merge = Thm.merge_thms)\<close>

consts Qc :: "nat \<Rightarrow> bool"  kx :: "('a, 'b) ring_scheme \<Rightarrow> nat"
axiomatization where kx_ax: "kx R = 0"
lemma X: "(0::nat) + 0 = 0" by simp
lemma tg [exported_premises 1]: "PROP A \<Longrightarrow> PROP A" .

context LF begin
lemma foo: "kx S = 0" by (rule kx_ax)
lemma t7: True by simp
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm t7}]))\<close>
context fixes y :: nat assumes "Qc y" begin
lemma t8: True by simp
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm t8}]))\<close>
end
declaration (pervasive) \<open>fn phi => Thm_Data.map (append (Morphism.fact phi [@{thm LF.foo}, @{thm X}]))\<close>
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
(* (d) *)
val d = find (fn th => Thm.eq_thm_prop (th, @{thm tg}));
val _ = \<^assert> (Thm.nprems_of d = 1 andalso Exported_Premises.count_of d = 1 andalso clean d);
(* (e) the newest entry (append puts the new facts in front), the stock export shape *)
val e = hd table;
val _ = \<^assert> (Thm.nprems_of e = Thm.nprems_of @{thm LF.foo} + 1 andalso Exported_Premises.count_of e = 0);
val _ = \<^assert> (not (Thm.eq_thm_prop (e, @{thm LF.foo})));
\<close>

end
