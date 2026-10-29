(* Plan section 7 test 6, the export layers of the setclass batch
   (ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md sections 3.2-3.3, 4): K is written where the light
   locale's own assumption is pasted, and counted layer by layer.  The theory copies of facts
   noted in LF's blocks: under a nested assumes layer (fresh: K 1; tagged: the nested layer takes
   K to 0, the light locale's layer adds one), a redeclaration stored as it is, a fixes-only
   block (no layer), a prop-valued defines (the layer keeps K), a layer whose only assumption is
   a sort constraint (K does not count it: the block's outer copy and the theory copy), a nested
   assumes "LFs T" against lemma (in LF) with the same assumption (K 1 both, two leading setclass
   premises); a predicate-free light locale (no layer: a fresh fact has no K, a tagged one keeps
   it, a nested assumes layer takes it to 0); the declaration path and syntax_declaration
   (pervasive), untagged and tagged, read from the leaf's own table at theory level. *)
theory Test6_Setclass_Layers
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>
ML \<open>structure Layer_Data = Generic_Data (type T = thm list val empty = [] val merge = Thm.merge_thms)\<close>
consts Pc :: 'a  Qc :: 'a  Sc :: 'a
axiomatization where Pc_ax: "Pc x y" and Pc1_ax: "Pc x" and Sc_ax: "Sc x"
light_locale LFs = fixes T :: "'a set" assumes fin: "finite T"
light_locale SetX = fixes n :: nat

context LF begin
lemma foo: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" by (rule conjI)
lemma e2 [setclass 2]: "A \<Longrightarrow> A \<Longrightarrow> A" by assumption
end

(* a nested assumes layer *)
context LF begin
context fixes y :: nat assumes hy: "Qc y" begin
lemma n1: "Pc S y" by (rule Pc_ax)
local_setup \<open>Local_Theory.note ((\<^binding>\<open>n2\<close>, []), @{thms LF.foo}) #> snd\<close>
lemmas n3 = LF.e2
declaration (pervasive) \<open>fn phi => Layer_Data.map (append (Morphism.fact phi [@{thm LF.e2}]))\<close>
end
end

(* fixes only *)
context LF begin
context fixes v :: nat begin
local_setup \<open>Local_Theory.note ((\<^binding>\<open>x1\<close>, []), @{thms LF.foo}) #> snd\<close>
end
end

(* a prop-valued defines *)
context LF begin
context fixes A B :: bool and x :: "prop" defines x_def: "x \<equiv> (A \<Longrightarrow> B)" begin
lemma d0: "PROP x \<Longrightarrow> PROP x" .
local_setup \<open>Local_Theory.note ((\<^binding>\<open>d1\<close>, []), [Setclass.put 1 @{thm d0}]) #> snd\<close>
end
end

(* a layer whose only assumption is a sort constraint; the block's outer copy (command S) *)
context LF begin
context assumes "SORT_CONSTRAINT('z::type)" begin
local_setup \<open>Local_Theory.note ((\<^binding>\<open>s1\<close>, []), @{thms LF.foo}) #> snd\<close>
end
ML \<open>check_rows [("SC morphism route", fn () =>
  Setclass.count_of @{thm s1} = 1 andalso Thm.nprems_of @{thm s1} = 3)]\<close>
end

(* a nested assumption that is a setclass premise, and lemma (in) with the same assumption *)
context LF begin
context fixes T :: "nat set" assumes "LFs T" begin
lemma w1: "Pc S T" by (rule Pc_ax)
end
end
lemma (in LF) w2: assumes "LFs (T :: nat set)" shows "Pc S T" by (rule Pc_ax)

(* a light locale without a predicate *)
context SetX begin
lemma p0: "n = n" by (rule refl)
local_setup \<open>Local_Theory.note ((\<^binding>\<open>p1\<close>, []), @{thms LF.foo}) #> snd\<close>
context assumes hn: "0 < n" begin
local_setup \<open>Local_Theory.note ((\<^binding>\<open>p2\<close>, []), @{thms LF.foo}) #> snd\<close>
end
end

(* declarations; the syntax declarations last *)
context LF begin
declaration (pervasive) \<open>fn phi => Layer_Data.map (append (Morphism.fact phi [@{thm Pc1_ax}]))\<close>
syntax_declaration (pervasive) \<open>fn phi => Layer_Data.map (append (Morphism.fact phi [@{thm Sc_ax}]))\<close>
syntax_declaration (pervasive) \<open>fn phi => Layer_Data.map (append (Morphism.fact phi [@{thm LF.e2}]))\<close>
end

(* command X: the theory copies and the theory's table *)
ML \<open>
local
  val ctxt = \<^context>;
  val table = Layer_Data.get (Context.Theory \<^theory>);
  fun entry t = the_single (filter (fn th => same_shape (Thm.prop_of th, Logic.varify_global t)) table);
  val k_of = Setclass.count_of;
  val count_sc = Light_Locale_Axiom_Facts.count_setclass_prems ctxt;
in
val _ = check_rows
 [("nested untagged", fn () => k_of @{thm LF.n1} = 1 andalso Thm.nprems_of @{thm LF.n1} = 2),
  ("nested tagged", fn () => k_of @{thm LF.n2} = 1 andalso Thm.nprems_of @{thm LF.n2} = 5),
  ("nested stored as is", fn () =>
     Thm.eq_thm_prop (@{thm LF.n3}, @{thm LF.e2}) andalso k_of @{thm LF.n3} = 3),
  ("fixes-only tagged", fn () => k_of @{thm LF.x1} = 2 andalso Thm.nprems_of @{thm LF.x1} = 4),
  ("defines tagged", fn () => k_of @{thm LF.d1} = 2 andalso
     same_shape (Thm.prop_of @{thm LF.d1},
       Logic.varify_global \<^prop>\<open>LF S \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close>)),
  ("SC function route", fn () => k_of @{thm LF.s1} = 2 andalso Thm.nprems_of @{thm LF.s1} = 4),
  ("setclass assumes", fn () => k_of @{thm LF.w1} = 1 andalso count_sc @{thm LF.w1} = 2),
  ("lemma (in) assumes", fn () => k_of @{thm LF.w2} = 1 andalso count_sc @{thm LF.w2} = 2),
  ("no predicate fresh", fn () => not (has_K_tag @{thm SetX.p0})),
  ("no predicate tagged", fn () => k_of @{thm SetX.p1} = 1 andalso
     same_shape (Thm.prop_of @{thm SetX.p1}, Thm.prop_of @{thm LF.foo})),
  ("no predicate nested", fn () =>
     not (has_K_tag @{thm SetX.p2}) andalso Thm.nprems_of @{thm SetX.p2} = 4),
  ("decl untagged", fn () => k_of (entry \<^prop>\<open>LF S \<Longrightarrow> Pc x\<close>) = 1),
  ("syntax decl untagged", fn () => k_of (entry \<^prop>\<open>LF S \<Longrightarrow> Sc x\<close>) = 1),
  ("syntax decl tagged", fn () =>
     k_of (entry \<^prop>\<open>LF S \<Longrightarrow> LF Sa \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A\<close>) = 4),
  ("decl nested tagged", fn () =>
     k_of (entry \<^prop>\<open>LF S \<Longrightarrow> Qc (y::nat) \<Longrightarrow> LF Sa \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A\<close>) = 1)]
end
\<close>

end
