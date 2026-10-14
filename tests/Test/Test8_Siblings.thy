(* Plan section 7 test 8 (declaration shapes), the sibling-import rows: the same parameter name in
   two imports (Heavy_Def with q == f x, Heavy_Par with a plain q) in both orders against their
   heavy controls, the explicit "f x", the D20 table and parameters (H with for a b t, interpret in a
   proof, the H0/LF2 controls), out-of-order defines (X1 + X2 through Y) and the cycle, the D20 table
   written twice in one proof, Nat_Par and H0', the sibling position recording f q, the applied-lhs
   defines in two spellings with eta-modulo acceptance and the stored values, the N fixture
   (abbreviations unfolded in the check) and the UPm sibling-position rows. *)
theory Test8_Siblings
  imports Test_Support
begin

ML \<open>
open Test_Support;
val strip = XML.content_of o YXML.parse_body;
(*the declaration must fail with exactly this message*)
fun fails_with expected f =
  ((f (); error "accepted") handle ERROR msg =>
    if strip msg = expected then () else error ("got:\n" ^ strip msg ^ "\nexpected:\n" ^ expected));
fun fails_prefix expected f =
  ((f (); error "accepted") handle ERROR msg =>
    if String.isPrefix expected (strip msg) then () else error ("got:\n" ^ strip msg));
fun defined_as ord y loc shown =
  "The " ^ ord ^ " parameter `" ^ y ^ "` of locale `" ^ loc ^ "` is defined as `" ^ shown ^
    "` and cannot be instantiated. You must write `_`.";
fun not_bound x t loc =
  "A light locale does not support definitions. `" ^ x ^ " \<equiv> " ^ t ^ "` from locale `" ^ loc ^
    "` is unfolded and `" ^ x ^ "` is not bound here. Write `" ^ t ^ "` instead.";
fun light thy text = fn () => light_locale_cmd text thy;
fun heavy thy text = fn () => locale_cmd text thy;
fun params thy l = map (fn ((x, T), mx) => (x, T, Mixfix.equal (mx, NoSyn))) (Locale.params_of thy l);
fun loc thy n = Locale.check_global thy (n, Position.none);
(*the morphism of the edge from parent p to l, and the instances of p's parameters under it*)
fun edge thy p l =
  the (find_first (fn {source, target, ...} => source = loc thy p andalso target = loc thy l)
    (Locale.dest_dependencies [] thy)) |> #morphism;
fun instances thy p l = Locale.instance_of thy (loc thy p) (edge thy p l);
fun tfrees ts = fold Term.add_tfrees ts [];

fun declares thy text = #2 (with_warnings (fn () => light_locale_cmd text thy));
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
  ML_val \<open>\<^assert> (null (#2 (with_warnings (fn () => Syntax.read_term \<^context> "Sq q"))))\<close>
  show True ..
qed
light_locale LF0 = Heavy_Def
ML \<open>
val thy = \<^theory>;
val _ = fails_with (not_bound "q" "a b" "Heavy_Def") (heavy thy "H0 = LF0 a b for a b + assumes \"Sq q\"");
val _ = fails_with (not_bound "q" "f x" "Heavy_Def") (light thy "LF2 = Heavy_Def + M2 q");
\<close>

(* out-of-order defines through Y; the cycle *)
locale X1 = fixes f :: "nat \<Rightarrow> nat" and a b :: nat defines "a \<equiv> f b"
locale X2 = fixes g :: "nat \<Rightarrow> nat" and b c :: nat defines "b \<equiv> g c"
locale Y = X1 + X2
light_locale LFY = Y
light_locale LFX = X1 + X2
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (nth (instances thy "Y" (loc thy "LFY")) 1 aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) ((g :: nat \<Rightarrow> nat) c)\<close>);
(*the control without Y: a's instance is f b, b being the shared parameter name*)
val _ = \<^assert> (nth (instances thy "X1" (loc thy "LFX")) 1 aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) (b :: nat)\<close>);
(*the cyclic defines are rejected by stock itself (a THM exception in the heavy declaration)*)
val _ = \<^assert> (not (can (heavy thy "Xc = fixes f g :: \"nat \<Rightarrow> nat\" and a b :: nat defines \"a \<equiv> f b\" and \"b \<equiv> g a\"") ()));
\<close>

(* the D20 table written twice in one proof; two instances in one header *)
lemma True
proof -
  interpret I: LF0 h 5 by unfold_locales (rule Rq_ax)
  interpret J: LF0 h 7 by unfold_locales (rule Rq_ax)
  ML_val \<open>\<^assert> (#2 (with_warnings (fn () => Syntax.read_term \<^context> "Sq q")) =
    ["The parameter `q` from locale `Heavy_Def` is not bound any more and treated as a fresh variable here."])\<close>
  show True ..
qed
light_locale LF2i = A: LF0 s u + B: LF0 t v for s t u v

(* Nat_Par, H0', and the sibling position recording f q *)
locale Nat_Par = fixes x :: nat assumes "x = x"
light_locale LF0n = Heavy_Def + Nat_Par x
ML \<open>
val thy = \<^theory>;
val _ = fails_with (not_bound "q" "g 5" "Heavy_Def") (heavy thy "H0' = LF0n g 5 for g + assumes \"Sq q\"");
\<close>
light_locale LFsib = Heavy_Par + Heavy_Def _ q
ML \<open>
val thy = \<^theory>;
val _ = \<^assert> (List.last (instances thy "Heavy_Def" (loc thy "LFsib")) aconv \<^term>\<open>(f :: nat \<Rightarrow> nat) (q :: nat)\<close>);
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
(*the shown term is the eta-contracted form, printed with the (+) notation of plus*)
val _ = fails_with (defined_as "2nd" "add" "AL2" "\<lambda>a. (+) (wrap a)") (light thy "LX = AL2 wrap \"\<lambda>a b. plus (wrap b) a\" for wrap");
\<close>
locale ALp = fixes g :: "'a \<Rightarrow> nat \<Rightarrow> nat" and x :: nat and y :: "'a \<Rightarrow> nat" defines "y a \<equiv> g a x"
light_locale LALp = ALp where y = "\<lambda>(a::'a). g a x"
locale ALb = fixes g :: "bool \<Rightarrow> 'b" and x :: nat and y :: "bool \<Rightarrow> 'b" defines "y a \<equiv> g a"
ML \<open>
val thy = \<^theory>;
val _ = ((light thy "LX = ALb where y = \"\<lambda>(a::nat). g a\"" (); error "accepted")
  handle ERROR m => \<^assert> (not (String.isPrefix "The " (strip m))));
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
val _ = ((light thy "LX = NL \"{x. x}\"" (); error "accepted") handle ERROR m => \<^assert> (not (String.isPrefix "The " (strip m))));
val _ = fails_with (defined_as "2nd" "B" "UPm" "fs {x. x \<noteq> 0}") (light thy "LX = UPm \"{x. x \<noteq> 0}\" \"fs {x. x = 0}\"");
\<close>

end
