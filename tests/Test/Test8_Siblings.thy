(* Plan section 7 test 8 (declaration shapes), the sibling-import rows: the same parameter name in
   two imports (Heavy_Def with q == f x, Heavy_Par with a plain q) in both orders against their
   heavy controls, the explicit "f x", the D20 table and parameters (H with for a b t, interpret in a
   proof, the H0/LF2 rows writing the eliminated q: the use warning, then stock's closure or
   stock's free-variable error), out-of-order defines (X1 + X2 through Y) and the cyclic defines
   (plan lines 5036 and 5080: the cycle across two imports, Yc = X1 + X2c, which stock accepts, is
   rejected by the light declaration with the section-6 definition error, with and without a
   same-named sibling parameter; a cycle of three with a definition hanging off it (Y3) and two
   separate cycles (Yc2); the single-locale cycle is rejected by stock itself, recorded), the
   D20 table written twice in one proof and the same inside LF0's block, a theory-level
   global_interpretation after which the use warning does not appear, Nat_Par and H0', the sibling
   position recording f q, the applied-lhs defines in two spellings with eta-modulo acceptance and
   the stored values (the shown fourth slot prints with the (+) notation, section 11 (31)), the N
   fixture (abbreviations unfolded in the check) and the UPm sibling-position rows; the rows where
   the plan asks for stock's type error assert its "Type unification failed" prefix. *)
theory Test8_Siblings
  imports Test_Support
begin

ML \<open>
open Test_Support;
val use_warning_q = eliminated_name_warning "q" "Heavy_Def";
val illegal_q = "Illegal free variables in expression: \"q\"";
\<close>

consts Rq :: "nat \<Rightarrow> bool"  Pq :: "nat \<Rightarrow> bool"  Sq :: "nat \<Rightarrow> bool"
axiomatization where Rq_ax: "Rq n" and Pq_ax: "Pq n"
locale Heavy_Def = fixes f :: "nat \<Rightarrow> nat" and x q :: nat defines "q \<equiv> f x" assumes hd: "Rq q"
locale Heavy_Par = fixes q :: nat assumes hp: "Pq q"
locale Heavy_Def' = fixes f :: "nat \<Rightarrow> nat" and x :: nat assumes hd: "Rq (f x)"
locale M2 = fixes m :: nat assumes "m = m"

ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (declares thy "LFs1 = Heavy_Def + Heavy_Par" = ["The following definitions from `Heavy_Def` are unfolded.\n  q \<equiv> f x"]);
\<close>
light_locale LFs1 = Heavy_Def + Heavy_Par
light_locale LFs2 = Heavy_Par + Heavy_Def
light_locale LFx = Heavy_Def + Heavy_Par "f x"
locale Hs1 = Heavy_Def' + Heavy_Par
locale Hs2 = Heavy_Par + Heavy_Def'

ML \<open>
val thy = \<^theory>;
fun pnames l = map (#1 o #1) (Locale.params_of thy (loc thy l));
val _ = \<^assert> (pnames "LFs1" = ["f", "x", "q"] andalso pnames "LFs2" = ["q", "f", "x"] andalso pnames "LFx" = ["f", "x"]);
val _ = \<^assert> (pnames "LFs1" = pnames "Hs1" andalso pnames "LFs2" = pnames "Hs2");
val _ = \<^assert> (#1 (Locale.specification_of thy (loc thy "LFs1")) = SOME \<^prop>\<open>LFs1 f x q\<close>);
val _ = \<^assert> (#1 (Locale.specification_of thy (loc thy "LFs2")) = SOME \<^prop>\<open>LFs2 q f x\<close>);
val _ = \<^assert> (null (#2 (Locale.specification_of thy (loc thy "LFs1"))));
val _ = \<^assert> (#2 (Logic.dest_equals (Thm.prop_of @{thm LFs1_def})) aconv Logic.varify_global \<^term>\<open>Heavy_Def f x \<and> Heavy_Par q\<close>);
\<close>

(* the D20 table and parameters *)
locale H = LFs1 a b t for a b t + assumes "Sq q"
locale Hh = Hs1 a b t for a b t + assumes "Sq q"
ML \<open>
val thy = \<^theory>;
fun assumes l = maps (fn Element.Assumes asms => maps (map #1 o #2) asms | _ => []) (Locale.hyp_spec_of thy (loc thy l));
val _ = \<^assert> (eq_list (op aconv) (assumes "H", assumes "Hh"));
val _ = \<^assert> (assumes "H" = [\<^prop>\<open>\<And>q. Sq q\<close>]);
\<close>
lemma True
proof -
  interpret I: LFs1 a b t by unfold_locales (simp_all add: Rq_ax Pq_ax)
  ML_prf \<open>val _ = \<^assert> (null (#2 (with_warnings (fn () => Syntax.read_term \<^context> "Sq q"))))\<close>
  show True ..
qed
light_locale LF0 = Heavy_Def
ML \<open>val thy = \<^theory>\<close>
(*the eliminated q in a heavy child's element: the use warning, q closed (user 2026-10-16 (a));
  at a light child's instance position: the warning, then stock's free-variable error*)
ML \<open>local
val ((h0, thy'), ws) = accepted (heavy thy "H0 = LF0 a b for a b + assumes \"Sq q\"");
val _ = \<^assert> (ws = [use_warning_q] andalso maps #2 (assumes_of thy' h0) = [\<^prop>\<open>\<And>q. Sq q\<close>]);
in end\<close>
ML \<open>val _ = \<^assert> (member (op =) (rejected illegal_q (light thy "LF2 = Heavy_Def + M2 q")) use_warning_q)\<close>

(* out-of-order defines through Y; the cyclic defines *)
locale X1 = fixes f :: "nat \<Rightarrow> nat" and a b :: nat defines "a \<equiv> f b"
locale X2 = fixes g :: "nat \<Rightarrow> nat" and b c :: nat defines "b \<equiv> g c"
locale Y = X1 + X2
light_locale LFY = Y
light_locale LFX = X1 + X2
locale X2c = fixes g :: "nat \<Rightarrow> nat" and b a :: nat defines "b \<equiv> g a"
locale Yc = X1 + X2c
locale Pb0 = fixes b :: nat
locale X3 = fixes k :: "nat \<Rightarrow> nat" and c a :: nat defines "c \<equiv> k a"
locale X4 = fixes h :: "nat \<Rightarrow> nat" and d a :: nat defines "d \<equiv> h a"
locale Y3 = X1 + X2 + X3 + X4
locale X5 = fixes p :: "nat \<Rightarrow> nat" and u v :: nat defines "u \<equiv> p v"
locale X6 = fixes r :: "nat \<Rightarrow> nat" and v u :: nat defines "v \<equiv> r u"
locale Yc2 = X1 + X2c + X5 + X6
ML \<open>local
val thy = \<^theory>;
val _ = \<^assert> (nth (instances thy "Y" (loc thy "LFY")) 1 aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) ((g :: nat \<Rightarrow> nat) c)\<close>);
(*the control without Y: a's instance is f b, b being the shared parameter name*)
val _ = \<^assert> (nth (instances thy "X1" (loc thy "LFX")) 1 aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) (b :: nat)\<close>);
(*the cycle across the two imports: stock accepts Yc (two definitions), the light declaration
  reports the section-6 definition error (the full-text row pins the template, the locale slot
  and the definition slots, printed from the parent's original bodies in their parameter order),
  also with the same-named sibling parameter of Pb0*)
val _ = \<^assert> (length (#2 (Locale.specification_of thy (loc thy "Yc"))) = 2);
val _ = fails_with ("A light locale does not support definitions. The definitions `a \<equiv> f b` and " ^
  "`b \<equiv> g a` from locale `Yc` refer to each other in a cycle and cannot be unfolded.") (light thy "LFc = Yc");
val _ = fails_prefix "A light locale does not support definitions. The definitions `" (light thy "LFc' = Yc + Pb0");
(*recorded (section 11 (31)): the single-locale cycle is rejected by stock itself, with a THM
  exception from the notes export*)
val _ = \<^assert> ((heavy thy "Xc = fixes f g :: \"nat \<Rightarrow> nat\" and a b :: nat defines \"a \<equiv> f b\" and \"b \<equiv> g a\"" (); false)
  handle THM _ => true);
in end\<close>
(*a cycle of three, a -> b -> c -> a, and d, which depends on the cycle without being on it:
  only the cycle is listed, joined "x, y and z"*)
ML \<open>local
val thy = \<^theory>;
val _ = \<^assert> (length (#2 (Locale.specification_of thy (loc thy "Y3"))) = 4);
val _ = fails_with ("A light locale does not support definitions. The definitions `a \<equiv> f b`, " ^
  "`b \<equiv> g c` and `c \<equiv> k a` from locale `Y3` refer to each other in a cycle and cannot be unfolded.")
  (light thy "LFc3 = Y3");
in end\<close>
(*two separate cycles: only the first in parameter order is listed (user 2026-10-17, U3 (A))*)
ML \<open>local
val thy = \<^theory>;
val _ = \<^assert> (length (#2 (Locale.specification_of thy (loc thy "Yc2"))) = 4);
val _ = fails_with ("A light locale does not support definitions. The definitions `a \<equiv> f b` and " ^
  "`b \<equiv> g a` from locale `Yc2` refer to each other in a cycle and cannot be unfolded.") (light thy "LFc2 = Yc2");
in end\<close>

(* the D20 table written twice in one proof; the same inside LF0's block; two instances in one
   header *)
lemma True
proof -
  interpret I: LF0 h 5 by unfold_locales (rule Rq_ax)
  interpret J: LF0 h 7 by unfold_locales (rule Rq_ax)
  ML_prf \<open>val _ = \<^assert> (#2 (with_warnings (fn () => Syntax.read_term \<^context> "Sq q")) = [use_warning_q])\<close>
  show True ..
qed
context LF0 begin
lemma True
proof -
  interpret I: LF0 h 5 by unfold_locales (rule Rq_ax)
  interpret J: LF0 h 7 by unfold_locales (rule Rq_ax)
  ML_prf \<open>val _ = \<^assert> (#2 (with_warnings (fn () => Syntax.read_term \<^context> "Sq q")) = [use_warning_q])\<close>
  show True ..
qed
end
light_locale LF2i = A: LF0 s u + B: LF0 t v for s t u v

(* Nat_Par, H0' (the table entry two hops away: the same warning), and the sibling position
   recording f q *)
locale Nat_Par = fixes x :: nat assumes "x = x"
light_locale LF0n = Heavy_Def + Nat_Par x
ML \<open>val thy = \<^theory>\<close>
ML \<open>local
val ((h0', thy'), ws) = accepted (heavy thy "H0' = LF0n g 5 for g + assumes \"Sq q\"");
val _ = \<^assert> (ws = [use_warning_q] andalso maps #2 (assumes_of thy' h0') = [\<^prop>\<open>\<And>q. Sq q\<close>]);
in end\<close>
light_locale LFsib = Heavy_Par + Heavy_Def _ q
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (List.last (instances thy "Heavy_Def" (loc thy "LFsib")) aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) (q :: nat)\<close>);
(*stock rejects the same-parent heavy twin: the missing position becomes Heavy_Par's q and the
  defines reads q == f q (primitive_defs.ML:69-70), so there is no twin to project*)
val _ = fails_prefix "Entity to be defined occurs on rhs" (heavy thy "Hsib = Heavy_Par + Heavy_Def _ q");
\<close>

(* applied-lhs defines *)
locale AL = fixes g :: "nat \<Rightarrow> nat \<Rightarrow> nat" and x :: nat and y :: "nat \<Rightarrow> nat" defines "y a \<equiv> g a x"
light_locale LAL = AL
light_locale LAL1 = AL where y = "\<lambda>a. g a x"
light_locale LAL2 = AL g x "\<lambda>a. g a x" for g x
locale AL2 = fixes wrap :: "nat \<Rightarrow> nat" and add :: "nat \<Rightarrow> nat \<Rightarrow> nat" defines "\<And>a b. add a b \<equiv> plus (wrap a) b"
light_locale LA2 = AL2
light_locale LA2e = AL2 wrap "\<lambda>a. plus (wrap a)" for wrap
light_locale LA2f = AL2 wrap "\<lambda>a b. plus (wrap a) b" for wrap
ML \<open>
val thy = \<^theory>;
val yinst = List.last (instances thy "AL" (loc thy "LAL"));
val _ = \<^assert> (yinst aconv \<^term>\<open>\<lambda>a. (g :: nat \<Rightarrow> nat \<Rightarrow> nat) a (x :: nat)\<close> andalso (case yinst of Abs _ => true | _ => false) andalso not (Term.loose_bvar (yinst, 0)));
val _ = \<^assert> (instances thy "AL" (loc thy "LAL1") = instances thy "AL" (loc thy "LAL") andalso instances thy "AL" (loc thy "LAL2") = instances thy "AL" (loc thy "LAL"));
val _ = \<^assert> (List.last (instances thy "AL2" (loc thy "LA2")) aconv \<^term>\<open>\<lambda>a b. plus ((wrap :: nat \<Rightarrow> nat) a) b\<close>);
val _ = \<^assert> (List.last (instances thy "AL2" (loc thy "LA2e")) aconv \<^term>\<open>\<lambda>a. plus ((wrap :: nat \<Rightarrow> nat) a)\<close>);
val _ = \<^assert> (List.last (instances thy "AL2" (loc thy "LA2f")) aconv \<^term>\<open>\<lambda>a b. plus ((wrap :: nat \<Rightarrow> nat) a) b\<close>);
(*the shown term is the eta-contracted form, printed with the (+) notation of plus (plan line 5042
  writes plus; the same term, section 11 (31))*)
val _ = fails_with (defined_as "2nd" "add" "AL2" "\<lambda>a. (+) (wrap a)") (light thy "LX = AL2 wrap \"\<lambda>a b. plus (wrap b) a\" for wrap");
\<close>
locale ALp = fixes g :: "'a \<Rightarrow> nat \<Rightarrow> nat" and x :: nat and y :: "'a \<Rightarrow> nat" defines "y a \<equiv> g a x"
light_locale LALp = ALp where y = "\<lambda>(a::'a). g a x"
locale ALb = fixes g :: "bool \<Rightarrow> 'b" and x :: nat and y :: "bool \<Rightarrow> 'b" defines "y a \<equiv> g a"
ML \<open>
val thy = \<^theory>;
val _ = fails_prefix "Type unification failed" (light thy "LX = ALb where y = \"\<lambda>(a::nat). g a\"");
\<close>

(* abbreviations are unfolded in the check: the N fixture; sibling positions with syntax: UPm *)
locale NL = fixes N :: "nat set" defines "N \<equiv> {x. x \<noteq> 0}"
light_locale LN1 = NL "{x. x \<noteq> 0}"
light_locale LN2 = NL "{x. \<not> x = 0}"
consts fs :: "nat set \<Rightarrow> nat set"
locale UPm = fixes A :: "nat set" and B :: "nat set" defines "B \<equiv> fs A"
light_locale LU1 = UPm "{x. x \<noteq> 0}" "fs {x. x \<noteq> 0}"
light_locale LU2 = UPm "{x. x \<notin> {}}" _
light_locale LU3 = UPm "{x. case x of 0 \<Rightarrow> True | _ \<Rightarrow> False}" _
ML \<open>
val thy = \<^theory>;
val _ = fails_with (defined_as "1st" "N" "NL" "{x. x \<noteq> 0}") (light thy "LX = NL \"{x. x \<noteq> 1}\"");
val _ = fails_prefix "Type unification failed" (light thy "LX = NL \"{x. x}\"");
val _ = fails_with (defined_as "2nd" "B" "UPm" "fs {x. x \<noteq> 0}") (light thy "LX = UPm \"{x. x \<noteq> 0}\" \"fs {x. x = 0}\"");
\<close>

(* a theory-level global_interpretation: no use warning afterwards (plan line 5005) *)
global_interpretation G: LF0 Suc 5 by unfold_locales (rule Rq_ax)
ML \<open>\<^assert> (null (#2 (with_warnings (fn () => Syntax.read_term (Proof_Context.init_global \<^theory>) "Sq q"))))\<close>

end
