(* Plan section 7 test 6, the fork-shape leaf (plan lines 4294-4309): the rows whose stored shape
   depends on whether the proof was forked.  This leaf runs twice -- in Light_Locale_Test (forked
   proofs: the result of a forked proof has every block assumption among its hyps, Goal.future_result)
   and, re-processed by the Serial_Wrapper of Light_Locale_Test_Serial, with parallel_proofs = 0
   (hyps are the assumptions the proof used).  The evidence rows pin the shape observed in each
   mode (first build 2026-10-13, section 11); the gate rows hold in both modes.
   Evidence rows: tq (statement names the light predicate itself, against the convention of
   decision 9 (i)), bad2, foo5, the bare lemma (in LF) fa8 [OF LF.ax], lemma (in Grp) l whose proof
   uses no Grp fact.  Gate rows: tq' (same statement as tq, proof started with insert LF_axioms),
   the nested-block writing l' of l, inductive ip inside Grp's block (Grp.ip.intros led by Grp ?G,
   K 1; the local copy Sub ?H G ==> Grp.ip G ?H with K 0 and no tag), the same declaration in the
   predicate-free Nop. *)
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
\<close>

consts Sc :: 'a  Pc :: 'a
axiomatization C :: bool where C_ax: C
axiomatization where Sc_ax: "Sc x" and Pc_ax: "Pc x y"

context LF begin

lemma ax: "Pc S y" by (rule Pc_ax)

lemma tq [case_names a, consumes 1]: "Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C"
  by (rule conjI, assumption, rule C_ax)

lemma tq' [case_names a, consumes 1]: "Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C"
  apply (insert LF_axioms) by (rule conjI, assumption, rule C_ax)

lemma bad2: "LF q \<Longrightarrow> Sc x" by (rule Sc_ax)

lemma foo5 [case_names a, consumes 1]: "Q \<Longrightarrow> LF S \<Longrightarrow> C" by (rule C_ax)

end

lemma (in LF) fa8 [OF LF.ax]: "Pc S y \<Longrightarrow> Pc S y \<and> C"
  by (rule conjI, assumption, rule C_ax)

ML \<open>
val _ = \<^assert> (shape @{thm LF.ax} (\<^prop>\<open>LF S \<Longrightarrow> Pc S y\<close>, 1));

(* gate: two LF premises and K 1 in both modes *)
val _ = \<^assert> (shape @{thm LF.tq'} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C\<close>, 1));

(* evidence: forked, the block assumption is among the hyps and is exported on top of the
   statement's own LF premise; serial, the statement is already in exported form *)
val _ = \<^assert>
  (if fork
   then shape @{thm LF.tq} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF q \<Longrightarrow> Q \<and> C\<close>, 1) andalso
     #2 (Rule_Cases.get @{thm LF.tq}) = 2
   else shape @{thm LF.tq} (\<^prop>\<open>Q \<Longrightarrow> LF (q :: ('c, 'd) ring_scheme) \<Longrightarrow> Q \<and> C\<close>, 0) andalso
     #2 (Rule_Cases.get @{thm LF.tq}) = 1);
val _ = \<^assert> (map (#1 o #1) (#1 (Rule_Cases.get @{thm LF.tq})) = ["a"]);
val _ = \<^assert>
  (if fork
   then shape @{thm LF.bad2} (\<^prop>\<open>LF S \<Longrightarrow> LF q \<Longrightarrow> Sc x\<close>, 1)
   else shape @{thm LF.bad2} (\<^prop>\<open>LF (q :: ('c, 'd) ring_scheme) \<Longrightarrow> Sc (x :: 'e)\<close>, 0));
val _ = \<^assert>
  (if fork
   then shape @{thm LF.foo5} (\<^prop>\<open>LF S \<Longrightarrow> Q \<Longrightarrow> LF S \<Longrightarrow> C\<close>, 1) andalso
     #2 (Rule_Cases.get @{thm LF.foo5}) = 2
   else shape @{thm LF.foo5} (\<^prop>\<open>Q \<Longrightarrow> LF S \<Longrightarrow> C\<close>, 0) andalso
     #2 (Rule_Cases.get @{thm LF.foo5}) = 1);
val _ = \<^assert>
  (if fork
   then shape @{thm LF.fa8} (\<^prop>\<open>LF S \<Longrightarrow> LF S \<Longrightarrow> Pc S y \<and> C\<close>, 1)
   else shape @{thm LF.fa8} (\<^prop>\<open>LF S \<Longrightarrow> Pc S y \<and> C\<close>, 0));
\<close>


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

ML \<open>
(* evidence *)
val _ = \<^assert>
  (if fork
   then shape @{thm Grp.l} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Sub H G\<close>, 1)
   else shape @{thm Grp.l} (\<^prop>\<open>Sub H (G :: 'x set) \<Longrightarrow> Sub H G\<close>, 0));

(* gate: the nested writing exports both layers' assumptions in either mode *)
val _ = \<^assert> (shape @{thm Grp.l'} (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Sub H G\<close>, 2));

(* gate: the package's result goes through the block's fp_def and carries the block's hyps *)
val _ = \<^assert> (shape (the_single @{thms Grp.ip.intros})
  (\<^prop>\<open>Grp (G :: 'x set) \<Longrightarrow> Sub H G \<Longrightarrow> Grp.ip G H\<close>, 1));
\<close>


(* the same declaration in a light locale without a predicate *)

light_locale Nop = fixes G :: "'x set"

context Nop begin
inductive ipn where ipnI: "Sub H G \<Longrightarrow> ipn H"
end

ML \<open>
val th = the_single @{thms Nop.ipn.intros};
val _ = \<^assert> (shape th (\<^prop>\<open>Sub H (G :: 'x set) \<Longrightarrow> Nop.ipn G H\<close>, 0));
val _ = \<^assert> (not (has_K_tag th));
\<close>

end
