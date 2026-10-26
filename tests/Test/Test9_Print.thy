(* Plan section 7 test 9 (structure): reading and printing on the gate fixture (plan 5096-5108,
   5111-5113): the bare operator prints bare, an explicit index of another structure stays, the
   two layers side by side in H' = LF + A and H = A + LF, the nested (structure) block, the
   translation-defined index syntax and a fixed variable's index syntax (both elided, section 11
   (39)), the value as an ordinary argument, the placeholder at an index position, the typed
   comparison (plan 5258-5261: the j / k pair on a value holding UNIV), the clean row, the
   placeholder-by-name row (plan 5262) and find_theorems (plan 5263-5265). *)
theory Test9_Print
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;

val golden = golden_line \<^theory> "structures.golden";

(*option off: the printed text has no default marker, the printer marks nothing bad, and the
  text reads back (up to eta: the printer contracts)*)
fun sound ctxt text =
  let val t = reads ctxt text in
    \<^assert> (not (String.isSubstring "_struct" (shows ctxt t)) andalso
      not (has_bad_markup ctxt t) andalso
      Envir.eta_contract (reads ctxt (shows ctxt t)) aconv Envir.eta_contract t)
  end;

(*every match: no limit (the default find_theorems_limit of 40 would truncate)*)
fun found ctxt goal criteria =
  Find_Theorems.find_theorems ctxt goal (SOME 100000) true criteria
  |> #2 |> map (Thm_Name.print o #1);
fun pattern ctxt text = Find_Theorems.Pattern (Proof_Context.read_term_pattern ctxt text);
fun has_fact_named suffix = exists (String.isSuffix suffix);
\<close>


subsection \<open>The gate fixture: bare prints bare, other indices stay (plan 5096-5099)\<close>

context LF
begin

lemma fooS: "x \<otimes> y = x \<otimes> y" by (rule refl)
lemma fooE: "a \<otimes> b = c \<Longrightarrow> (a \<otimes> b = c \<Longrightarrow> Q) \<Longrightarrow> Q" by blast

ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (NONE, SOME (reads ctxt "UP S")));
val _ = prints_as ctxt "x \<otimes> y" "x \<otimes> y";
val _ = prints_as ctxt "Q (x \<otimes>\<^bsub>S\<^esub> y) \<otimes> z" "Q (x \<otimes>\<^bsub>S\<^esub> y) \<otimes> z";
val _ = prints_as ctxt "x \<otimes>\<^bsub>S\<^esub> y" (golden "otimes_S");
val _ = List.app (sound ctxt) ["inj_on (m_inv (UP S)) A", "\<lambda>x. inv x", "inv x"];
val _ = \<^assert> (round_trips ctxt (reads ctxt "x \<otimes> y"));

(*the translation-defined index syntax: read on UP S, printed bare as the inner operator (plan
  5111-5113; section 11 (33) syntax-2 lifted by (39)), the same as a PIDE print (show_markup, the
  one print setting that differs)*)
val _ = \<^assert> (reads ctxt "\<Oplus>i\<in>A. u i \<otimes> v i" aconv
  reads ctxt "\<Oplus>\<^bsub>UP S\<^esub>i\<in>A. u i \<otimes>\<^bsub>UP S\<^esub> v i");
val _ = prints_as ctxt "\<Oplus>i\<in>A. u i \<otimes> v i" "\<Oplus>i\<in>A. u i \<otimes> v i";
val _ = \<^assert> (round_trips ctxt (reads ctxt "\<Oplus>i\<in>A. u i \<otimes> v i"));
val _ = \<^assert> (shows (Config.put show_markup true ctxt) (reads ctxt "\<Oplus>i\<in>A. u i \<otimes> v i") = "\<Oplus>i\<in>A. u i \<otimes> v i");

(*clean (plan 5261): with show_types the repeated S inside the index argument UP S is wrapped by
  prune_types; the comparison still finds the implicit structure*)
val _ = \<^assert> (not (String.isSubstring "\<^bsub>"
  (shows (Config.put show_types true ctxt) (reads ctxt "x \<otimes> y = y \<otimes> x"))));

(*find_theorems (plan 5263-5265): the bare pattern denotes UP S with the block's fixed S, which
  the exported LF.fooS (on UP ?S) does not match -- the block's copy does; the wildcard index and
  intro find LF.fooS; elim on a goal whose premise matches finds the block's copy fooE, whose
  major premise matches, and not LF.fooE, whose major premise is LF ?S*)
fun by_pattern text = found ctxt NONE [(true, pattern ctxt text)];
val bare = by_pattern "_ \<otimes> _";
val wildcard = by_pattern "_ \<otimes>\<^bsub>_\<^esub> _";
val goal = Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt "x \<otimes> y = x \<otimes> y"));
val intro = found ctxt (SOME goal) [(true, Find_Theorems.Intro)];
val goal' = Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt "x \<otimes> y = z \<Longrightarrow> R"));
val elim = found ctxt (SOME goal') [(true, Find_Theorems.Elim)];
val _ =
  if not (has_fact_named "LF.fooS" bare) andalso has_fact_named "local.fooS" bare andalso
    has_fact_named "LF.fooS" wildcard andalso has_fact_named "LF.fooS" intro andalso
    has_fact_named "local.fooE" elim andalso not (has_fact_named "LF.fooE" elim)
  then ()
  else error ("find_theorems:\n  bare: " ^ commas bare ^ "\n  wildcard: " ^ commas wildcard ^
    "\n  intro: " ^ commas intro ^ "\n  elim: " ^ commas elim);
in end\<close>

(*the value as an ordinary argument prints as itself*)
ML \<open>val _ = prints_as \<^context> "carrier (UP S)" "carrier (UP S)"\<close>
(*the value strictly inside an index argument prints as itself too: only a direct child of
  _index becomes the empty subscript*)
ML \<open>local
val ctxt = \<^context>;
val _ = prints_as ctxt "x \<otimes>\<^bsub>f (UP S)\<^esub> y" "x \<otimes>\<^bsub>f (UP S)\<^esub> y";
val _ = \<^assert> (round_trips ctxt (reads ctxt "x \<otimes>\<^bsub>f (UP S)\<^esub> y"));
in end\<close>

(*the placeholder at an index position is the default structure by name: at the constant's own
  index syntax and at the translation-defined one*)
ML \<open>local
val ctxt = \<^context>;
val value = reads ctxt "UP S";
fun with_placeholder text =
  Term.subst_free [(value, Free (Syntax_Trans.implicit_structure_, fastype_of value))] (reads ctxt text);
val _ = \<^assert> (shows ctxt (with_placeholder "x \<otimes>\<^bsub>UP S\<^esub> y") = "x \<otimes> y");
val _ = \<^assert> (shows ctxt (with_placeholder "(\<Oplus>\<^bsub>UP S\<^esub>i\<in>A. p i i) = q") = "(\<Oplus>i\<in>A. p i i) = q");
in end\<close>

(*a fixed variable with index syntax: its index position is elided like a constant's*)
context
  fixes F :: "('a, nat \<Rightarrow> 'a) up_ring \<Rightarrow> nat \<Rightarrow> nat" (\<open>\<Phi>\<index> _\<close> [1000] 999)
begin
ML \<open>local
val ctxt = \<^context>;
val _ = prints_as ctxt "\<Phi>\<^bsub>UP S\<^esub> x" "\<Phi> x";
val _ = \<^assert> (round_trips ctxt (reads ctxt "\<Phi>\<^bsub>UP S\<^esub> x"));
in end\<close>
end

end

context D
begin

lemma fooS: "x \<otimes> y = x \<otimes> y" by (rule refl)
lemma fooE: "a \<otimes> b = c \<Longrightarrow> (a \<otimes> b = c \<Longrightarrow> Q) \<Longrightarrow> Q" by blast

ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (SOME "P", NONE));
(*the heavy block's local copy matches the bare pattern*)
val _ = \<^assert> (has_fact_named "local.fooS" (found ctxt NONE [(true, pattern ctxt "_ \<otimes> _")]));
in end\<close>

end


subsection \<open>The two layers side by side (plan 5100-5104, 5107)\<close>

context H'
begin
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (SOME "G", SOME (reads ctxt "UP S")));
val _ = prints_as ctxt "x \<otimes>\<^bsub>G\<^esub> y" (golden "otimes_G");
val _ = prints_as ctxt "x \<otimes> y" "x \<otimes> y";
val _ = \<^assert> (forall (round_trips ctxt o reads ctxt) ["x \<otimes>\<^bsub>G\<^esub> y", "x \<otimes> y"]);
val _ = prints_as ctxt "x \<otimes>\<^bsub>S\<^esub> y" (golden "otimes_S");
(*the under-applied inverse keeps its argument, no bare G appears*)
val _ = \<^assert> (not (String.isSubstring "G" (shows ctxt (reads ctxt "inj_on (m_inv (UP S)) A"))));
val _ = \<^assert> (round_trips ctxt (reads ctxt "inj_on (m_inv (UP S)) A"));
in end\<close>
end

(* the finite sum needs a ring: a variant of A over a ring_scheme *)
locale Ar = fixes G :: "('a, 'b) ring_scheme" (structure)
locale H'r = LF + Ar
context H'r
begin
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (SOME "G", SOME (reads ctxt "UP S")));
val _ = prints_as ctxt "\<Oplus>\<^bsub>G\<^esub>i\<in>A. u i \<otimes>\<^bsub>G\<^esub> v i" (golden "finsum_G");
in end\<close>
end

context H
begin
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (SOME "G", NONE));
val _ = \<^assert> (bare_denotes ctxt "G");
val _ = prints_as ctxt "x \<otimes> y" "x \<otimes> y";
in end\<close>
end


subsection \<open>A (structure) variable fixed inside the light block (plan 5101-5103, 5108)\<close>

context LF
begin
context
  fixes T :: "('c, 'd) monoid_scheme" (structure)
begin
ML \<open>local
val ctxt = \<^context>;
val _ = \<^assert> (layers ctxt = (SOME "T", SOME (reads ctxt "UP S")));
(*the bare operator is the implicit structure's; the first layer's head keeps its subscript*)
val _ = \<^assert> (bare_denotes ctxt "UP S");
val _ = prints_as ctxt "x \<otimes>\<^bsub>T\<^esub> y" (golden "otimes_T");
val _ = prints_as ctxt "x \<otimes> y" "x \<otimes> y";
(*the value strictly inside the index argument: a mark resolved anywhere under _index would
  print the silently wrong x \<otimes>\<^bsub>f T\<^esub> y*)
val _ = prints_as ctxt "x \<otimes>\<^bsub>f (UP S)\<^esub> y" "x \<otimes>\<^bsub>f (UP S)\<^esub> y";
val _ = \<^assert> (round_trips ctxt (reads ctxt "x \<otimes>\<^bsub>f (UP S)\<^esub> y"));
in end\<close>
end
end


subsection \<open>A closed constant instance and the typed comparison (plan 5258-5261)\<close>

locale UPi =
  fixes P :: "int monoid" (structure)
  defines "P \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>"
light_locale LFi = UPi
locale Di = UPi

context LFi
begin
ML \<open>local
val ctxt = \<^context>;
val int_monoid = reads ctxt "\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr> :: int monoid";
val _ = \<^assert> (layers ctxt = (NONE, SOME int_monoid));
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = (0 :: int)\<rparr>\<^esub> y");
val _ = \<^assert> (Term.add_frees t [] = [("y", \<^typ>\<open>int\<close>), ("x", \<^typ>\<open>int\<close>)]);
in end\<close>
context
  fixes j :: int
begin
ML \<open>local
val ctxt = \<^context>;
(*the index argument equals the implicit structure, type included: elided although the value
  holds an abbreviation (UNIV); the same as a PIDE print*)
val text = "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\<^esub> = j";
val _ = prints_as ctxt text "\<one> = j";
val _ = \<^assert> (round_trips ctxt (reads ctxt text));
val _ = \<^assert> (shows (Config.put show_markup true ctxt) (reads ctxt text) = "\<one> = j");
in end\<close>
end
context
  fixes k :: nat
begin
ML \<open>local
val ctxt = \<^context>;
(*the index argument differs from the implicit structure only in its type: it stays -- the pair
  with the j row: a comparison blind to types breaks one of the two*)
val text = "\<one>\<^bsub>\<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>\<^esub> = k";
val _ = prints_as ctxt text (golden "one_int_monoid");
val _ = \<^assert> (round_trips ctxt (reads ctxt text));
in end\<close>
end
end

context Di
begin
ML \<open>
val _ = \<^assert> (filter (member (op =) ["x", "y"] o #1) (Term.add_frees (reads \<^context> "x \<otimes> y") []) =
  [("y", \<^typ>\<open>int\<close>), ("x", \<^typ>\<open>int\<close>)]);
\<close>
end


subsection \<open>The placeholder is recognised by name, not by a typed comparison (plan 5262)\<close>

ML \<open>
val _ =
  fails_checked "a type error naming the operator, never the placeholder"
    (fn msg =>
      String.isPrefix "Type unification failed" msg andalso String.isSubstring "\<otimes>" msg andalso
      not (String.isSubstring "implicit_structure_" msg))
    (light \<^theory> "LFte = UP_cring S for S + assumes \"x \<otimes> y = True\"");
\<close>

end
