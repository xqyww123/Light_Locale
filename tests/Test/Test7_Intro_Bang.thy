(* Plan section 7 test 7: the two polarities of intro! on the predicate fact (decision 11, section 5.7).  (1) The adversarial shape sharing ?n: two registrations' predicate facts LQ a1 and LQ a2 coexist as [intro!], the goal KG is provable only with the second instance -- auto and blast succeed (intro! does not fix the instance).  (2) The other polarity (the shape of Axioms_Intro_Bang_Fast_Probe): goal EX y. LFi y & Q y, the premise-free intro! fact LFi a of the light block next to the unsafe intro rules LFi (g c) and Q (g c) -- fastforce fails, auto and blast succeed; in the heavy twin (plain Di_axioms with a hand-added [intro]) fastforce succeeds. *)
theory Test7_Intro_Bang
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts QG :: "nat \<Rightarrow> bool"  WW :: "nat \<Rightarrow> bool"  KG :: bool  a1 :: nat  a2 :: nat
light_locale LQ = fixes p :: nat assumes "QG p"
axiomatization where ax_QG_a1: "QG a1" and ax_QG_a2: "QG a2" and ax_WW: "WW a2"
  and ax_key: "\<And>n. LQ n \<Longrightarrow> WW n \<Longrightarrow> KG"
interpretation IQ1: LQ a1 by unfold_locales (rule ax_QG_a1)
interpretation IQ2: LQ a2 by unfold_locales (rule ax_QG_a2)

ML \<open>
fun proves tac ctxt prop = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => tac context)) ();
val ctxt = Proof_Context.init_global \<^theory> addIs @{thms ax_WW ax_key};
val _ = \<^assert> (proves Clasimp.auto_tac ctxt \<^prop>\<open>KG\<close>);
val _ = \<^assert> (proves (fn c => blast_tac c 1) ctxt \<^prop>\<open>KG\<close>);
\<close>

consts P :: "nat \<Rightarrow> bool"  Q :: "nat \<Rightarrow> bool"  c :: nat  g :: "nat \<Rightarrow> nat"
light_locale LFi = fixes a :: nat assumes "P a"
locale Di = fixes a :: nat assumes "P a"
axiomatization where hb_g: "LFi (g c)" and hb_gD: "Di (g c)" and qg: "Q (g c)"

context LFi begin
ML_val \<open>
val ctxt = \<^context> addIs @{thms hb_g qg};
val goal = \<^prop>\<open>\<exists>y. LFi y \<and> Q y\<close>;
val _ = \<^assert> (not (proves (fn c => Clasimp.fast_force_tac c 1) ctxt goal));
val _ = \<^assert> (proves Clasimp.auto_tac ctxt goal);
val _ = \<^assert> (proves (fn c => blast_tac c 1) ctxt goal);
\<close>
end

context Di begin
ML_val \<open>
val ctxt = \<^context> addIs @{thms Di_axioms hb_gD qg};
val goal = \<^prop>\<open>\<exists>y. Di y \<and> Q y\<close>;
val _ = \<^assert> (proves (fn c => Clasimp.fast_force_tac c 1) ctxt goal);
\<close>
end

end
