(* Facts reached through a light edge carry no definition hyp (plan section 11, implementation-period
   change (11)).  A light header eliminates every defined parameter of its imports and stores no
   defs; gen_add_locale proves the inherited equations, reflexive under the edge morphism, and its
   b_satisfy discharges them.  Before that fix every fact reached through such an edge carried
   t == t, measured 2026-10-13 (ai-artifacts/Step1_Probe_elim_def_hyp.thy).
   Each row asserts that the named facts have no hyp beyond the assumptions of the context, and
   where a user would hit the bug, uses the fact in a proof.  All fixtures are local to this leaf
   with distinct names; the only registrations that meet are the deliberately sequenced I/J pair
   and I6 (a dependency added after a light registration). *)
theory Test_Eliminated_Defines
  imports Test_Support
begin

ML \<open>
fun assert_clean ctxt names =
  names |> List.app (fn name =>
    (case Test_Support.extra_hyps ctxt name of
      [] => ()
    | ts => error ("Undischarged hyps of " ^ name ^ ": " ^
        commas (map (Syntax.string_of_term ctxt) ts))));
\<close>

(* the probe: declaration block, reopened context, interpret in proofs, theory-level interpretation *)
locale Pd2 = fixes x :: nat and y :: nat defines "y \<equiv> x + 1" assumes pos: "y > 0"
locale Q2 = fixes z :: nat assumes "z > 0"
sublocale Pd2 \<subseteq> q: Q2 y by unfold_locales (rule pos)

light_locale LG = Pd2 x _ for x
begin
lemma blk: "Q2 (x + 1)" by (rule q.Q2_axioms)
ML \<open>val _ = assert_clean \<^context> ["q.Q2_axioms"]\<close>
end

context LG begin
lemma reopened: "Q2 (x + 1)" by (rule q.Q2_axioms)
end

lemma init: "LG x \<Longrightarrow> Q2 (x + 1)"
proof -
  assume "LG x"
  then interpret LG x .
  show ?thesis by (rule q.Q2_axioms)
qed

lemma init2: "Q2 (34 + 1)"
proof -
  interpret K: LG 34 unfolding LG_def Pd2_def by simp
  show ?thesis by (rule K.q.Q2_axioms)
qed

interpretation I: LG 3 unfolding LG_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["I.q.Q2_axioms", "I.Pd2_axioms"]\<close>

(* cross-registration upgrade of Pd2 3 (3 + 1) by a heavy interpretation; J brings its own
   witnesses, so this row does not pin the fix *)
interpretation J: Pd2 3 "3 + 1" by unfold_locales simp_all
ML \<open>val _ = assert_clean \<^context> ["J.q.Q2_axioms", "J.pos", "I.q.Q2_axioms"]\<close>
lemma (in Pd2) later1: "y = x + 1" by (simp add: y_def)
ML \<open>val _ = assert_clean \<^context> ["J.later1"]\<close>

(* upgrade inside one roundup: Pd2 x (x + 1) is reached first through the light edge
   (Syntax_only), then at Full; the upgrade re-descends with the first morphism *)
locale H3 = LG
sublocale H3 \<subseteq> pf: Pd2 x "x + 1" by unfold_locales simp_all
context H3 begin
lemma "0 < x + 1" by (rule pos)
ML \<open>val _ = assert_clean \<^context> ["pos", "q.Q2_axioms"]\<close>
end
interpretation IH3: H3 40 unfolding H3_def LG_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["IH3.pos", "IH3.q.Q2_axioms"]\<close>
lemma (in Pd2) later3: "y = x + 1" by (simp add: y_def)
ML \<open>val _ = assert_clean \<^context> ["IH3.later3"]\<close>

(* a kept written position *)
light_locale LK = Pd2 x "x + 1" for x
interpretation K: LK 5 unfolding LK_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["K.q.Q2_axioms"]\<close>

(* nested eliminations *)
locale Pn = fixes x y w :: nat defines "y \<equiv> x + 1" and "w \<equiv> y * 2" assumes wpos: "w > 0"
sublocale Pn \<subseteq> qn: Q2 w by unfold_locales (rule wpos)
light_locale LN = Pn x _ _ for x
context LN begin
lemma "Q2 ((x + 1) * 2)" by (rule qn.Q2_axioms)
end
interpretation N: LN 3 unfolding LN_def Pn_def by simp
ML \<open>val _ = assert_clean \<^context> ["N.qn.Q2_axioms"]\<close>

(* a definition stated pointwise (stored closed under a meta-quantifier); polymorphic definitions,
   with the type fixed at the edge and generic *)
locale Q3 = fixes g :: "nat \<Rightarrow> nat" assumes "g 0 > 0"
locale Pf = fixes c :: nat and f :: "nat \<Rightarrow> nat" defines "f n \<equiv> n + c" assumes fpos: "f 0 > 0"
sublocale Pf \<subseteq> q3: Q3 f by unfold_locales (rule fpos)
light_locale LFn = Pf c _ for c
interpretation Fn: LFn 1 unfolding LFn_def Pf_def by simp
ML \<open>val _ = assert_clean \<^context> ["Fn.q3.Q3_axioms"]\<close>

locale Pg = fixes f :: "'a \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'a"
  defines "g a \<equiv> f (f a)" assumes inj: "inj g"
locale Qf = fixes h :: "'b \<Rightarrow> 'b" assumes "inj h"
sublocale Pg \<subseteq> qf: Qf g by unfold_locales (rule inj)
light_locale LPg = Pg f _ for f :: "nat \<Rightarrow> nat"
context LPg begin
lemma "Qf (\<lambda>a. f (f a))" by (rule qf.Qf_axioms)
ML \<open>val _ = assert_clean \<^context> ["qf.Qf_axioms"]\<close>
end
light_locale LPh = Pg f _ for f
interpretation IPh: LPh Suc unfolding LPh_def Pg_def by (simp add: inj_def)
ML \<open>val _ = assert_clean \<^context> ["IPh.qf.Qf_axioms"]\<close>

(* eta: a kept position eta-different from the body; a body that is an eta-redex *)
locale Qe = fixes h :: "nat \<Rightarrow> nat" assumes "h 0 > 0"
locale Pe = fixes g f :: "nat \<Rightarrow> nat" defines "f \<equiv> g" assumes epos: "f 0 > 0"
sublocale Pe \<subseteq> qe: Qe f by unfold_locales (rule epos)
light_locale LE = Pe g "\<lambda>n. g n" for g
context LE begin
ML \<open>val _ = assert_clean \<^context> ["qe.Qe_axioms"]\<close>
end
interpretation IE: LE Suc unfolding LE_def Pe_def by simp
ML \<open>val _ = assert_clean \<^context> ["IE.qe.Qe_axioms"]\<close>
locale Pe2 = fixes f :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat"
  defines "g \<equiv> \<lambda>a. f a" assumes ig: "inj g"
sublocale Pe2 \<subseteq> qe2: Qf g by unfold_locales (rule ig)
light_locale LPe = Pe2 f _ for f
interpretation IPe: LPe Suc unfolding LPe_def Pe2_def by (simp add: inj_def)
ML \<open>val _ = assert_clean \<^context> ["IPe.qe2.Qf_axioms"]\<close>

(* a lambda instantiation applied by the definition: the hyp is a beta-redex *)
locale Pa = fixes f :: "nat \<Rightarrow> nat" and y :: nat defines "y \<equiv> f 0" assumes ypos: "y > 0"
sublocale Pa \<subseteq> qa: Q2 y by unfold_locales (rule ypos)
light_locale LPa = Pa "\<lambda>n. n + k" _ for k
context LPa begin
ML \<open>val _ = assert_clean \<^context> ["qa.Q2_axioms"]\<close>
end
interpretation IPa: LPa 2 unfolding LPa_def Pa_def by simp
ML \<open>val _ = assert_clean \<^context> ["IPa.qa.Q2_axioms"]\<close>

(* heavy importing light; light importing light *)
locale H = LG
context H begin
lemma "Q2 (x + 1)" by (rule q.Q2_axioms)
end
interpretation HH: H 7 unfolding H_def LG_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["HH.q.Q2_axioms"]\<close>
light_locale LL = LG
context LL begin
lemma "Q2 (x + 1)" by (rule q.Q2_axioms)
end
interpretation L: LL 9 unfolding LL_def LG_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["L.q.Q2_axioms"]\<close>

(* sublocale into and out of a light locale *)
locale R = fixes a :: nat assumes "a > 2"
sublocale R \<subseteq> lg: LG a unfolding LG_def Pd2_def by simp
context R begin
lemma "Q2 (a + 1)" by (rule lg.q.Q2_axioms)
end
interpretation RR: R 4 by unfold_locales simp
ML \<open>val _ = assert_clean \<^context> ["RR.lg.q.Q2_axioms"]\<close>
locale Q4 = fixes u :: nat assumes "u \<noteq> 0"
sublocale LG \<subseteq> q4: Q4 "x + 1" by unfold_locales simp
interpretation I4: LG 11 unfolding LG_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["I4.q4.Q4_axioms", "I4.q.Q2_axioms"]\<close>

(* a dependency added to the parent after a light registration exists (add_dependency) *)
locale Q6 = fixes z :: nat assumes "z \<noteq> 0"
interpretation I6: LG 60 unfolding LG_def Pd2_def by simp
sublocale Pd2 \<subseteq> q6: Q6 y by unfold_locales (simp add: pos)
ML \<open>val _ = assert_clean \<^context> ["I6.q6.Q6_axioms", "J.q6.Q6_axioms"]\<close>
context LG begin
lemma "Q6 (x + 1)" by (rule q6.Q6_axioms)
end

(* heavy chains: an inherited definition, own and inherited definitions, a renamed definition *)
locale Hc = Pd2 + fixes v :: nat assumes "v > y"
light_locale LHc = Hc x _ v for x v
interpretation IHc: LHc 1 5 unfolding LHc_def Hc_def Pd2_def Hc_axioms_def by simp
ML \<open>val _ = assert_clean \<^context> ["IHc.q.Q2_axioms"]\<close>
locale Hd = Pd2 a b for a b + fixes c :: nat defines "c \<equiv> b + 2"
light_locale LHd = Hd a _ _ for a
interpretation IHd: LHd 14 unfolding LHd_def Hd_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["IHd.q.Q2_axioms"]\<close>
locale Pr = Pd2 a b for a b
light_locale LR = Pr x _ for x
context LR begin
ML \<open>val _ = assert_clean \<^context> ["q.Q2_axioms"]\<close>
end

(* a sublocale target with its own defines; two instances of one parent *)
locale Q5 = fixes z w :: nat defines "w \<equiv> z * 2" assumes "w > 0"
sublocale Pd2 \<subseteq> q5: Q5 y "y * 2" by unfold_locales (simp_all add: pos)
light_locale LG5 = Pd2 x _ for x
interpretation I5: LG5 2 unfolding LG5_def Pd2_def by simp
ML \<open>val _ = assert_clean \<^context> ["I5.q5.Q5_axioms"]\<close>
light_locale L2 = Pd2 x _ + p2: Pd2 "x + 5" _ for x
context L2 begin
ML \<open>val _ = assert_clean \<^context> ["q.Q2_axioms", "p2.q.Q2_axioms"]\<close>
end

(* rewrites; a lemma (in LG) exported to the theory *)
interpretation ID: LG 50 rewrites "(50::nat) + 1 = 51" unfolding LG_def Pd2_def by simp_all
ML \<open>val _ = assert_clean \<^context> ["ID.q.Q2_axioms"]\<close>
lemma (in LG) ex1: "Q2 (x + 1)" by (rule q.Q2_axioms)
ML \<open>val _ = assert_clean \<^context> ["LG.ex1"]\<close>

(* heavy control: a heavy locale's facts keep its definition, as an assumption of its context *)
locale HP = Pd2 x y for x y + assumes "y > 1"
context HP begin
ML \<open>
  val _ = assert_clean \<^context> ["q.Q2_axioms"];
  val _ = \<^assert> (exists (fn t => t aconv @{prop "y \<equiv> x + 1"})
    (Thm.hyps_of @{thm q.Q2_axioms}));
\<close>
end

(* stock rejects a definition of a non-parameter, so every inherited definition sits at an
   eliminated (or kept) position and its reflexivity proof applies *)
ML \<open>
  val _ = \<^assert> (not (can (Test_Support.locale_cmd "Foo = fixes a :: nat defines \"b \<equiv> a + 1\"")
    \<^theory>))
\<close>

end
