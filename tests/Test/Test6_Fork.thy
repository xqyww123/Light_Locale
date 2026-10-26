(* Plan section 7 test 6, the fork-shape leaf (plan lines 4296-4311): the rows whose stored shape
   could depend on whether the proof was forked.  This leaf runs twice -- in Light_Locale_Test
   (forked proofs: the result of a forked proof has every block assumption among its hyps,
   Goal.future_result) and, re-processed by the Serial_Wrapper of Light_Locale_Test_Serial, with
   parallel_proofs = 0 (hyps are the assumptions the proof used).  Milestone 3's first item,
   second version: a new proof result is not a redeclaration, so it is always exported as in
   stock and every row holds the same value in both modes.
   tq (statement names the light predicate itself), bad2, foo5, the bare lemma (in LF) fa8
   [OF LF.ax], lemma (in Grp) l whose proof uses no Grp fact: LF ?S (Grp ?G) in front, K 1;
   tq' (same statement as tq, proof started with insert LF_axioms), the nested-block writing l'
   of l, inductive ip inside Grp's block (Grp.ip.intros led by Grp ?G, K 1; the local copy
   Sub ?H G ==> Grp.ip G ?H with K 0 and no tag), the same declaration in the predicate-free Nop.
   The final criterion (N18): e1s [exported_premises 2] gets LF ?S in front, K 3; a block-free
   theorem proved by Goal.prove_sorry and written back by declaration (pervasive) or
   Local_Theory.note gets LF ?S in front, K 1.  N27: the redeclaration bad2' = bad2 of a new
   proof result's local copy.  N29, the activated facts that depend on a witness: every witness
   proved by Isar carries the assumptions of its context (Element's witness proof), so the
   activated facts redeclared in a light block go the stock way in both modes -- rows A (light
   block), B (nested layer), D (sublocale in a light block), F (theory-level sublocale of a light
   locale), G (a heavy source locale's own sublocale chain), H (a light locale importing a heavy
   one with a sublocale edge), S (a subclass edge): LF ?S in front, K 1 (K 2 nested); C: a
   witness proved in a context without assumptions has no hyps, the fact is stored as itself,
   K 0; E (heavy block), T (theory-level assumes block), P and R (interpret in a proof): the
   activated fact's hyps are all the context's assumptions.  Every theory-level assertion is in
   the last ML command, evaluated row by row, which names each failing row. *)
theory Test6_Fork
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

(* plan section 7, session graph: the one mode assertion of the leaf *)
ML \<open>
open Test_Support;
val fork = Session.get_name () <> "Light_Locale_Test_Serial";
val _ = \<^assert> (Future.proofs_enabled 1 = fork);

fun shape th (prop, k) =
  Thm.prop_of th aconv Logic.varify_global prop andalso Exported_Premises.count_of th = k;

structure Fork_Data = Generic_Data (type T = thm list val empty = [] val merge = Thm.merge_thms);
\<close>

consts Sc :: 'a  Pc :: 'a
axiomatization C :: bool where C_ax: C
axiomatization where Sc_ax: "Sc x" and Pc_ax: "Pc x y"

(* N29's fixtures *)
locale Cw = fixes v :: nat assumes cv: "v = v"
lemma (in Cw) cl: "v + 0 = v" by simp
locale Cn = fixes v :: nat
lemma (in Cn) cn: "v + 0 = v" by simp
locale Cs = fixes v :: nat assumes cs: "v = v"
sublocale Cs \<subseteq> e: Cw "v + 1" by (rule Cw.intro) (rule refl)
locale Hh = fixes v :: nat assumes hh: "v = v"
sublocale Hh < hq: Cw "v + 3" by (rule Cw.intro) (rule refl)
light_locale LH = Hh
class sk0 = fixes skx :: 'a
class skb = sk0 + assumes skbx: "skx = skx"
class skc = sk0 + assumes skcx: "skx = skx"
subclass (in skb) skc by (rule class.skc.intro) (rule refl)
ML \<open>
val n29_p = Unsynchronized.ref false;
val n29_r = Unsynchronized.ref false;
\<close>

context LF begin

lemma ax: "Pc S y" by (rule Pc_ax)

lemma tq [case_names a, consumes 1]: "Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C"
  by (rule conjI, assumption, rule C_ax)

lemma tq' [case_names a, consumes 1]: "Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C"
  apply (insert LF_axioms) by (rule conjI, assumption, rule C_ax)

lemma bad2: "LF q \<Longrightarrow> Sc x" by (rule Sc_ax)

lemma foo5 [case_names a, consumes 1]: "Q \<Longrightarrow> LF S \<Longrightarrow> C" by (rule C_ax)

(* N18; e1s is a mechanism fixture, not a user scenario *)
lemma e1s [exported_premises 2]: "A \<Longrightarrow> A \<Longrightarrow> A" by assumption

local_setup \<open>fn lthy =>
  let
    val th = Goal.prove_sorry lthy [] [] \<^prop>\<open>Sc (0::nat)\<close> (fn {context, ...} => resolve_tac context @{thms Sc_ax} 1);
  in
    lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>}
        (fn phi => Fork_Data.map (append (Morphism.fact phi [th])))
    |> Local_Theory.note ((\<^binding>\<open>ps\<close>, []), [th]) |> snd
  end\<close>

(* N27 *)
lemmas bad2' = bad2

end

lemma (in LF) fa8 [OF LF.ax]: "Pc S y \<Longrightarrow> Pc S y \<and> C"
  by (rule conjI, assumption, rule C_ax)


(* two light locales without a heavy twin *)

light_locale Sub = fixes H G :: "'x set" assumes sub: "H \<subseteq> G"

light_locale Grp = fixes G :: "'x set" assumes grp: "G = G"

lemma (in Grp) l: assumes "Sub H G" shows "Sub H G" by (rule assms)

context Grp begin

context fixes H :: "'x set" assumes sg: "Sub H G" begin
lemma l': "Sub H G" by (rule sg)
end

inductive ip where ipI: "Sub H G \<Longrightarrow> ip H"

(* the local copy, by the hand-written shape: Sub ?H G ==> Grp.ip G ?H, G the block's Free *)
ML \<open>
val th = the_single @{thms ip.intros};
val _ = \<^assert> (Exported_Premises.count_of th = 0 andalso not (has_K_tag th));
val _ = \<^assert> (Thm.prop_of th aconv
  (\<^prop>\<open>Sub H G \<Longrightarrow> Grp.ip G H\<close> |> Term.map_aterms (fn Free ("H", T) => Var (("H", 0), T) | t => t)));
\<close>

end


(* the same declaration in a light locale without a predicate *)

light_locale Nop = fixes G :: "'x set"

context Nop begin
inductive ipn where ipnI: "Sub H G \<Longrightarrow> ipn H"
end


(* N29: the block commands; the values only readable inside a block are bound by ML (E, T) or
   written into a reference by ML_prf (P, R) and asserted in the last ML command *)

context LF begin
interpretation N: Cw 0 by (rule Cw.intro) (rule refl)
lemmas y_cl = N.cl
end

context Grp begin
context fixes H :: "'x set" assumes sg2: "Sub H G" begin
interpretation N2: Cw 0 by (rule Cw.intro) (rule refl)
lemmas yn_cl = N2.cl
end
end

context Grp begin
sublocale gw: Cw 1 by (rule Cw.intro) (rule refl)
lemmas ys_ax = gw.Cw_axioms
end

sublocale Grp \<subseteq> gs: Cw 2 by (rule Cw.intro) (rule refl)
context Grp begin
lemmas yg = gs.Cw_axioms
end

context LF begin
interpretation N4: Cs 2 by (rule Cs.intro) (rule refl)
lemmas y_e = N4.e.cl
end

context LH begin
lemmas yh = hq.Cw_axioms
end

context LF begin
interpretation Nsk: skb "0::nat" by (rule class.skb.intro) (rule refl)
lemmas y_sk = Nsk.skc_axioms
end

context D begin
interpretation N3: Cw 0 by (rule Cw.intro) (rule refl)
ML \<open>val n29_e = hyps_are_assms \<^context> @{thm N3.cl}\<close>
end

context fixes x :: nat assumes hx: "x = x" begin
interpretation N6: Cw 6 by (rule Cw.intro) (rule refl)
ML \<open>val n29_t = hyps_are_assms \<^context> @{thm N6.cl}\<close>
end

context D begin
notepad
begin
  interpret N5: Cw 5 by (rule Cw.intro) (rule refl)
  ML_prf \<open>n29_p := hyps_are_assms \<^context> @{thm N5.cl}\<close>
  interpret N7: Cw 7 rewrites r7: "(7::nat) + 0 = 7" by (rule Cw.intro, rule refl, simp)
  ML_prf \<open>n29_r := hyps_are_assms \<^context> @{thm r7}\<close>
end
end

context LF begin
interpretation M: Cn 0 .
lemmas z_cn = M.cn
end

context Nop begin
interpretation Nn: Cw 9 by (rule Cw.intro) (rule refl)
lemmas yn = Nn.cl
end


ML \<open>
val _ = check_rows
 [("ax", fn () => shape @{thm LF.ax} (\<^prop>\<open>LF S \<Longrightarrow> Pc S y\<close>, 1)),
  (* two LF premises and K 1, with or without insert LF_axioms *)
  ("tq'", fn () => shape @{thm LF.tq'} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C\<close>, 1)),
  ("tq", fn () => shape @{thm LF.tq} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C\<close>, 1) andalso
     #2 (Rule_Cases.get @{thm LF.tq}) = 2),
  ("tq case names", fn () => map (#1 o #1) (#1 (Rule_Cases.get @{thm LF.tq})) = ["a"]),
  ("bad2", fn () => shape @{thm LF.bad2} (\<^prop>\<open>LF S \<Longrightarrow> LF q \<Longrightarrow> Sc x\<close>, 1)),
  ("foo5", fn () => shape @{thm LF.foo5} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF S \<Longrightarrow> C\<close>, 1) andalso
     #2 (Rule_Cases.get @{thm LF.foo5}) = 2),
  ("fa8", fn () => shape @{thm LF.fa8} (\<^prop>\<open>LF S \<Longrightarrow> LF S \<Longrightarrow> Pc S y \<and> C\<close>, 1)),
  ("Grp.l", fn () => shape @{thm Grp.l} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Sub H G\<close>, 1)),
  (* the nested writing exports both layers' assumptions *)
  ("Grp.l'", fn () => shape @{thm Grp.l'} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Sub H G\<close>, 2)),
  (* the package's result goes through the block's fp_def and carries the block's hyps *)
  ("Grp.ip.intros", fn () => shape (the_single @{thms Grp.ip.intros})
     (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Grp.ip G H\<close>, 1)),
  ("Nop.ipn.intros", fn () =>
     shape (the_single @{thms Nop.ipn.intros}) (\<^prop>\<open>Sub H (G :: 'x set) \<Longrightarrow> Nop.ipn G H\<close>, 0) andalso
     not (has_K_tag (the_single @{thms Nop.ipn.intros}))),
  ("N18 e1s", fn () => shape @{thm LF.e1s} (\<^prop>\<open>LF S \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A\<close>, 3)),
  ("N18 declaration", fn () =>
     exists (fn th => shape th (\<^prop>\<open>LF S \<Longrightarrow> Sc (0::nat)\<close>, 1) andalso null (Thm.hyps_of th))
       (Fork_Data.get (Context.Theory \<^theory>))),
  ("N18 note", fn () => shape @{thm LF.ps} (\<^prop>\<open>LF S \<Longrightarrow> Sc (0::nat)\<close>, 1)),
  ("N27", fn () => shape @{thm LF.bad2'} (\<^prop>\<open>LF S \<Longrightarrow> LF q \<Longrightarrow> Sc x\<close>, 1)),
  ("N29 A", fn () => shape @{thm LF.y_cl} (\<^prop>\<open>LF S \<Longrightarrow> 0 + 0 = (0::nat)\<close>, 1)),
  ("N29 B", fn () => shape @{thm Grp.yn_cl} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> 0 + 0 = (0::nat)\<close>, 2)),
  ("N29 C", fn () => shape @{thm LF.z_cn} (\<^prop>\<open>0 + 0 = (0::nat)\<close>, 0) andalso not (has_K_tag @{thm LF.z_cn})),
  ("N29 D", fn () => shape @{thm Grp.ys_ax} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Cw (1::nat)\<close>, 1)),
  ("N29 E", fn () => n29_e),
  ("N29 F", fn () => shape @{thm Grp.yg} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Cw (2::nat)\<close>, 1)),
  ("N29 G", fn () => shape @{thm LF.y_e} (\<^prop>\<open>LF S \<Longrightarrow> (2::nat) + 1 + 0 = 2 + 1\<close>, 1)),
  ("N29 H", fn () => shape @{thm LH.yh} (\<^prop>\<open>LH v \<Longrightarrow> Cw (v + 3)\<close>, 1)),
  ("N29 S", fn () => shape @{thm LF.y_sk} (\<^prop>\<open>LF S \<Longrightarrow> class.skc (0::nat)\<close>, 1)),
  ("N29 T", fn () => n29_t),
  ("N29 P", fn () => ! n29_p),
  ("N29 R", fn () => ! n29_r),
  ("N29 N", fn () => shape @{thm Nop.yn} (\<^prop>\<open>(9::nat) + 0 = 9\<close>, 0))]
\<close>

end
