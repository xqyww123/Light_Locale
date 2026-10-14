(* Plan section 7 test 2 (declaration equivalence), part (a): a heavy fixture HB without defines,
   its heavy twin D and the light LF with the byte-identical header text.  The only theory-level
   registration (interpretation I: LF) is the last command. *)
theory Test2_Declaration
  imports Test_Support
begin

ML \<open>
structure T2_Flag = Generic_Data (type T = bool val empty = false fun merge (a, b) = a orelse b);
\<close>

locale HB = fixes a :: nat assumes hb: "a = a"

declaration (in HB) \<open>K (T2_Flag.put true)\<close>

lemma (in HB) hthm: "a + 0 = a" by simp

locale D = HB + fixes b :: nat assumes ax: "b = a"
begin
ML_val \<open>\<^assert> (Thm.prop_of @{thm ax} aconv @{prop "b = a"})\<close>
end

(* the short name ax is the local copy of LF's own header assumption, Thm.eq_thm_prop with D's *)
light_locale LF = HB + fixes b :: nat assumes ax: "b = a"
begin
ML_val \<open>\<^assert> (Thm.prop_of @{thm ax} aconv @{prop "b = a"})\<close>
end

ML \<open>
val thy = \<^theory>;
val lf = Locale.check_global thy ("LF", Position.none);
val d = Locale.check_global thy ("D", Position.none);
val hb = Locale.check_global thy ("HB", Position.none);
val _ = Test_Support.assert_twin thy (lf, d);

(*print_locale: only the head line and the name differ (the assumes line differs by the name)*)
fun lines show_facts loc =
  split_lines (Pretty.pure_string_of (Locale.pretty_locale thy show_facts loc));
val _ = \<^assert> (hd (lines false lf) = "light_locale LF" andalso hd (lines false d) = "locale D");
val _ = \<^assert> (tl (lines false lf) = map (space_implode "LF" o space_explode "D") (tl (lines false d)));

(*the fact names print_locale! shows: the quoted name on the line after each "notes"*)
fun printed_fact_names loc =
  let
    val ls = map (String.concat o space_explode " ") (lines true loc);
    fun quoted line =
      (case raw_explode line of
        "\"" :: cs => implode (take_prefix (fn c => c <> "\"") cs)
      | _ => error ("printed_fact_names: " ^ line));
  in map (quoted o #2) (filter (fn (l, _) => l = "notes") (ls ~~ tl (ls @ [""]))) end;
val lf_printed_facts = printed_fact_names lf;
val _ = \<^assert> (lf_printed_facts = ["HB_axioms", "LF_axioms"]);
\<close>

(* derivation name of the head fact: D.ax and LF.ax differ by D -> LF only *)
ML \<open>
val dn_lf = Thm.derivation_name @{thm LF.ax} and dn_d = Thm.derivation_name @{thm D.ax};
val _ = \<^assert> (#2 dn_lf = #2 dn_d andalso
  Long_Name.explode (#1 dn_lf) = map (fn "D" => "LF" | s => s) (Long_Name.explode (#1 dn_d)));
\<close>

(* tags through the public projection Locale.locale_notes *)
ML \<open>
fun assumes_names loc =
  maps (fn Element.Assumes asms => map (Binding.name_of o #1 o #1) asms | _ => [])
    (Locale.hyp_spec_of thy loc);
fun note_names loc = maps (map (Binding.name_of o #1 o #1) o #2) (Locale.locale_notes thy loc);
val A = assumes_names lf;
val _ = \<^assert> (A = ["ax"] andalso assumes_names d = A);
val _ = \<^assert> (not (exists (member (op =) A) (note_names lf)));
val _ = \<^assert> (filter_out (fn s => s = "") (note_names lf) = ["LF_axioms"]);
(*the standard locale: exactly one note for each name in A*)
val _ = \<^assert> (forall (fn a => length (filter (fn s => s = a) (note_names d)) = 1) A);
\<close>

(* edge directions through Locale.is_light at both ends: LF's edge to its heavy parent goes from a
   heavy source to a light target, the edge of a heavy child of LF from a light source *)
locale H = LF

ML \<open>
fun edge_ends tgt =
  Locale.dest_dependencies [] \<^theory>
  |> filter (fn {target, ...} => target = tgt)
  |> map (fn {source, target, ...} =>
      (Locale.is_light \<^theory> source, Locale.is_light \<^theory> target));
val _ = \<^assert> (edge_ends lf = [(false, true)]);
val _ = \<^assert> (edge_ends (Locale.check_global \<^theory> ("H", Position.none)) = [(true, false)]);
\<close>

context HB begin
ML_val \<open>\<^assert> (T2_Flag.get (Context.Proof \<^context>))\<close>
end

context LF begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (not (T2_Flag.get (Context.Proof ctxt)));
fun has_fact name = can (Proof_Context.get_fact ctxt) (Facts.named name);
val _ = \<^assert> (not (has_fact "ax"));
val _ = \<^assert> (has_fact "LF_axioms" andalso has_fact "LF.ax");
(*the fact names here equal those print_locale! LF shows*)
val _ = \<^assert>
  (map (Long_Name.base_name o #1)
    (Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
      (Proof_Context.facts_of ctxt)) |> sort_strings |> equal lf_printed_facts);
\<close>
end

(* a light child's block does not see the parent's local copy *)
light_locale LF2 = LF + fixes c :: nat assumes ax2: "c = b"
begin
ML_val \<open>\<^assert> (not (can (Proof_Context.get_fact \<^context>) (Facts.named "ax")))\<close>
end

(* header elements cannot refer to the light parent's head assumption by the short name *)
ML \<open>
val _ = \<^assert> (not (can (Test_Support.light_locale_cmd "LF3 = LF + notes h = ax") thy));
val _ = \<^assert> (not (can (Test_Support.locale_cmd "H3 = LF + notes h = ax") thy));
val _ = \<^assert> (can (Test_Support.locale_cmd "H3 = LF + notes h = LF.ax") thy);
\<close>

(* decision 10, polarity pair *)
(* hthm resolves but does not rewrite, so the head assumption gets no HB hyp (stock rejects one
   with "Undeclared hyps") *)
locale H10 = HB + fixes b :: nat assumes ax [simplified hthm]: "b = a"

ML \<open>
val _ =
  (Test_Support.light_locale_cmd "LF10 = HB + fixes b :: nat assumes ax [simplified hthm]: \"b = a\"" thy;
   error "LF10 accepted")
  handle ERROR msg =>
    \<^assert> (XML.content_of (YXML.parse_body msg) = "Undefined fact: \"hthm\"");
\<close>

(* part (b): a heavy fixture with defines; the light twin eliminates the defined position y *)
locale Pd = fixes g :: "nat \<Rightarrow> nat" and x :: nat and y :: nat defines "y \<equiv> g x"
  assumes pd: "y = g x"

locale Dd = Pd f v _ for f v
light_locale LFd = Pd f v _ for f v

ML \<open>
val lfd = Locale.check_global \<^theory> ("LFd", Position.none);
val dd = Locale.check_global \<^theory> ("Dd", Position.none);
val pl = Locale.params_of \<^theory> lfd and ph = Locale.params_of \<^theory> dd;
(*params_of LFd is the heavy twin's table without the eliminated y, in the same relative order*)
val _ = \<^assert> (map #1 pl = filter_out (fn (x, _) => x = "y") (map #1 ph));
val _ = \<^assert> (null (#2 (Locale.specification_of \<^theory> lfd)));
val _ = \<^assert> (not (null (#2 (Locale.specification_of \<^theory> dd))));
(*print_locale differs, besides the head and the name, in the fixes of y and the defines line*)
fun lines' loc = split_lines (Pretty.pure_string_of (Locale.pretty_locale \<^theory> false loc));
val _ = \<^assert> (lines' lfd =
  ["light_locale LFd", "  fixes f :: \"nat \092<Rightarrow> nat\"", "    and v :: \"nat\"",
   "  assumes \"LFd f v\""]);
val _ = \<^assert> (lines' dd =
  ["locale Dd", "  fixes y :: \"nat\"", "    and f :: \"nat \092<Rightarrow> nat\"", "    and v :: \"nat\"",
   "  assumes \"Dd f v\"", "  defines \"y \092<equiv> f v\""]);
\<close>

interpretation I: LF 0 0 by unfold_locales simp_all

ML_val \<open>\<^assert> (not (T2_Flag.get (Context.Proof \<^context>)))\<close>

end
