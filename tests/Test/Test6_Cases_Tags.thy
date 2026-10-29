(* Plan section 7 test 6, the hand-written tag rows (plan lines 4516-4536): foo [case_names a b,
   consumes 1] (local copy as the heavy block's, theory copy equal up to K with the pinned values),
   foo2 [params x y] (binders x y), foo2'' [params x y z] (fails on both sides with stock's message),
   foo8 [rotated, params x y], foo3 [cases_open, consumes 1]; r1/r2/r3 [cases pred: ipr] found by
   find_casesP, LF ?S first and LF.ipr ?S ?x second, r3 as r1. *)
theory Test6_Cases_Tags
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
consts Pc :: 'a  Qc :: 'a
axiomatization C :: bool where C_ax: C
axiomatization where Pc_ax: "Pc x y" and Qc1_ax: "Qc x"

ML \<open>
fun binders th = (case Thm.prems_of th of _ :: _ => map (fn p => map #1 (Logic.strip_params p)) (Thm.prems_of th) | [] => []);
(*foo2'' [params x y z] fails with stock's message, on either side*)
fun params_xyz_fails ctxt =
  (theorem_in ctxt (Binding.name "foo2''") "[params x y z]" "(\<And>a b. Q a b) \<Longrightarrow> C" (fn ctxt => resolve_tac ctxt @{thms C_ax}); false)
    handle ERROR msg => String.isPrefix "More names than parameters in subgoal!" (Protocol_Message.clean_output msg);
\<close>

(* r1, r2 and r3 are alpha-variants of each other: with the same proposition the Induct table
   would keep only the last one (Item_Net.update) *)
context D begin
inductive ipr :: "nat \<Rightarrow> bool" where "Pc S n \<Longrightarrow> ipr n"
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma foo2 [params x y]: "(\<And>a b. Q a b) \<Longrightarrow> C" by (rule C_ax)
lemma foo8 [rotated, params x y]: "Pc x \<Longrightarrow> (\<And>a b. Q a b) \<Longrightarrow> Qc x" by (rule Qc1_ax)
lemma foo3 [cases_open, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma r1 [case_names a b, consumes 1, cases pred: ipr]: "ipr x \<Longrightarrow> (x = 0 \<Longrightarrow> W) \<Longrightarrow> (x \<noteq> 0 \<Longrightarrow> W) \<Longrightarrow> W" by blast
lemma r2 [case_names a b, cases pred: ipr]: "ipr y \<Longrightarrow> (y = 0 \<Longrightarrow> V) \<Longrightarrow> (y \<noteq> 0 \<Longrightarrow> V) \<Longrightarrow> V" by blast
lemma r3 [case_names a b, cases pred: ipr, consumes 1]: "ipr z \<Longrightarrow> (z = 0 \<Longrightarrow> U) \<Longrightarrow> (z \<noteq> 0 \<Longrightarrow> U) \<Longrightarrow> U" by blast
ML \<open>val _ = \<^assert> (params_xyz_fails \<^context>)\<close>
ML \<open>val heavy = {foo = @{thm foo}, foo2 = @{thm foo2}, foo8 = @{thm foo8}, foo3 = @{thm foo3}, r1 = @{thm r1}, r2 = @{thm r2}, r3 = @{thm r3}};\<close>
end

context LF begin
inductive ipr :: "nat \<Rightarrow> bool" where "Pc S n \<Longrightarrow> ipr n"
lemma foo [case_names a b, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma foo2 [params x y]: "(\<And>a b. Q a b) \<Longrightarrow> C" by (rule C_ax)
lemma foo8 [rotated, params x y]: "Pc x \<Longrightarrow> (\<And>a b. Q a b) \<Longrightarrow> Qc x" by (rule Qc1_ax)
lemma foo3 [cases_open, consumes 1]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma r1 [case_names a b, consumes 1, cases pred: ipr]: "ipr x \<Longrightarrow> (x = 0 \<Longrightarrow> W) \<Longrightarrow> (x \<noteq> 0 \<Longrightarrow> W) \<Longrightarrow> W" by blast
lemma r2 [case_names a b, cases pred: ipr]: "ipr y \<Longrightarrow> (y = 0 \<Longrightarrow> V) \<Longrightarrow> (y \<noteq> 0 \<Longrightarrow> V) \<Longrightarrow> V" by blast
lemma r3 [case_names a b, cases pred: ipr, consumes 1]: "ipr z \<Longrightarrow> (z = 0 \<Longrightarrow> U) \<Longrightarrow> (z \<noteq> 0 \<Longrightarrow> U) \<Longrightarrow> U" by blast
ML \<open>
val _ = \<^assert> (params_xyz_fails \<^context>);
val _ = \<^assert> (plain_equal (@{thm foo}, #foo heavy));
val _ = \<^assert> (plain_equal (@{thm foo2}, #foo2 heavy) andalso plain_equal (@{thm foo8}, #foo8 heavy));
val _ = \<^assert> (binders @{thm foo2} = [["x", "y"]]);
\<close>
end

ML \<open>
(* foo: the theory copy up to K, pinned values *)
val (info_h, n_h) = Rule_Cases.get (#foo heavy) and (info_l, n_l) = Rule_Cases.get @{thm LF.foo};
val _ = \<^assert> (info_l = info_h andalso n_l = n_h + Setclass.count_of @{thm LF.foo});
val _ = \<^assert> (info_h = [(("a", []), []), (("b", []), [])] andalso n_h = 1 andalso n_l = 2);
val _ = \<^assert> (Thm.nprems_of (#foo heavy) = 2 andalso Thm.nprems_of @{thm LF.foo} = 3);
val _ = \<^assert> (Thm.prop_of @{thm LF.foo} aconv Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>);
val _ = \<^assert> (Setclass.count_of @{thm LF.foo} = 1);
(* foo2: the binders of the second premise are x y on both copies *)
val _ = \<^assert> (binders @{thm LF.foo2} = [[], ["x", "y"]]);
(* foo8: the theory copy *)
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.foo8},
  Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (\<And>x y. Q x y) \<Longrightarrow> Pc x \<Longrightarrow> Qc x\<close>));
val _ = \<^assert> (binders @{thm LF.foo8} = [[], ["x", "y"], []] andalso Setclass.count_of @{thm LF.foo8} = 1);
(* foo3 *)
val _ = \<^assert> (Rule_Cases.is_cases_open @{thm LF.foo3} andalso Setclass.lookup_consumes @{thm LF.foo3} = SOME 2
  andalso Setclass.count_of @{thm LF.foo3} = 1
  andalso Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of @{thm LF.foo3})));
(* r1-r3: equal up to K 1 to the twin's; r3 as r1 up to renaming, with the same tags but for the
   name tag (section 11, item (21)); each found under LF.ipr ?S ?x *)
val _ = \<^assert> (diff_K 1 (@{thm LF.r1}, #r1 heavy) andalso diff_K 1 (@{thm LF.r2}, #r2 heavy));
val tags_but_name = filter_out (fn (k, _) => k = Markup.nameN) o Thm.get_tags;
val _ = \<^assert> (same_shape (Thm.prop_of @{thm LF.r3}, Thm.prop_of @{thm LF.r1}) andalso
  tags_but_name @{thm LF.r3} = tags_but_name @{thm LF.r1});
val _ = List.app (fn th =>
    let val SOME e = induct_entry Induct.find_casesP \<^context> \<^prop>\<open>LF.ipr S x\<close> th in
      \<^assert> (Thm.eq_thm_prop (e, th));
      \<^assert> (Light_Locale_Axiom_Facts.is_light_prop \<^context> (hd (Thm.prems_of th)));
      \<^assert> ((case Term.strip_comb (HOLogic.dest_Trueprop (nth (Thm.prems_of th) 1)) of
        (Const (c, _), [Var _, Var _]) => Long_Name.base_name c = "ipr" | _ => false))
    end) [@{thm LF.r1}, @{thm LF.r2}, @{thm LF.r3}];
\<close>

end
