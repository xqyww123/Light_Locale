(* Plan section 7 test 7: the degeneracy warnings (decision 12), verbatim.  The name slot is the full name of the input fact (Local_Theory.full_name); an input without a name gets the sentence without the name slot (section 6).  Rows: a head assumption [simp]; the major-premise variant on the predicate-free S for the six elim/dest spellings (exactly the one degeneracy warning each, nothing else); the same on LHb with a predicate; the fused and split polarity rows on LH, the unnamed [simp] row and the re-declaration row declare LH.fooU [simp] in a reopened block; two package-internal rows (fun, inductive) with no warning. *)
theory Test7_Degeneracy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts Pd :: "'a \<Rightarrow> bool"  cc :: 'b
consts f1 :: "'a \<Rightarrow> 'a"  f2 :: "'a \<Rightarrow> 'a"  f3 :: "'a \<Rightarrow> 'a"  f4 :: "'a \<Rightarrow> 'a"
axiomatization where Pd_ax: "Pd x"

ML \<open>
fun ws f = #2 (with_warnings f);
fun warnings_equal expected got =
  if got = expected then ()
  else error ("warnings differ:\n" ^ cat_lines got ^ "\nexpected:\n" ^ cat_lines expected);
\<close>

(* a head assumption with [simp] *)
ML \<open>
val _ = warnings_equal ["Light locale rule `Test7_Degeneracy.LHs.ax` [simp]: its left-hand side is led by locale parameter `h` which will be a schematic variable in the system registry. The system simplifier may not work as you expect. Consider stating it on a derived constant."]
  (ws (fn () => light_locale_cmd "LHs = fixes h :: \"'a \<Rightarrow> 'b\" assumes ax [simp]: \"h x = cc\"" \<^theory>));
\<close>

(* the major-premise variant; the witness is the predicate-free S; one warning per spelling *)
light_locale S = fixes h :: "'a \<Rightarrow> bool"

ML \<open>
val _ = ["dest", "dest!", "dest?", "elim", "elim!", "elim?"] |> List.app (fn a =>
  let
    val kind = String.substring (a, 0, 4);
    val name = "foo_" ^ translate_string (fn "!" => "b" | "?" => "q" | c => c) a;
  in
    warnings_equal
      ["Light locale rule `Test7_Degeneracy.S." ^ name ^ "` [" ^ kind ^ "]: its major premise is led by locale parameter `h` which will be a schematic variable in the system registry. The system classical reasoner may not work as you expect. Consider stating it on a derived constant."]
      (ws (fn () => lemma_in "S" (Binding.name name) ("[" ^ a ^ "]") "h x \<Longrightarrow> Pd x"
        (fn ctxt => resolve_tac ctxt @{thms Pd_ax}) \<^theory>))
  end);
(*the conclusion of the intro variant is led by the constant Pd: no warning*)
val _ = ["intro", "intro!", "intro?"] |> List.app (fn a =>
  warnings_equal [] (ws (fn () => lemma_in "S" (Binding.name ("fooi_" ^ translate_string (fn "!" => "b" | "?" => "q" | c => c) a))
    ("[" ^ a ^ "]") "h x \<Longrightarrow> Pd x" (fn ctxt => resolve_tac ctxt @{thms Pd_ax}) \<^theory>)));
\<close>

(* the same shape with a predicate, proved in the declaration block from the local copy hP *)
light_locale LHb = fixes h :: "'a \<Rightarrow> bool" assumes hP: "\<And>x. h x \<Longrightarrow> Pd x"
begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    theorem_in lthy (Binding.name "food") "[dest]" "h x \<Longrightarrow> Pd x" (fn ctxt => resolve_tac ctxt @{thms hP}))
  in warnings_equal ["Light locale rule `Test7_Degeneracy.LHb.food` [dest]: its major premise is led by locale parameter `h` which will be a schematic variable in the system registry. The system classical reasoner may not work as you expect. Consider stating it on a derived constant."] w; lthy' end\<close>
end

(* the polarity rows: the fused [symmetric, simp] (simp sees h (f1 x) = cc), the split
   [simp, symmetric] (simp runs on the written statement, the stored fact is reversed), the
   unnamed lemma [simp], and declare LH.fooU [simp] in a reopened block *)
light_locale LH = fixes h :: "'a \<Rightarrow> 'b" assumes hc: "\<And>x. h x = cc"
begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    theorem_in lthy (Binding.name "foo_fused") "[symmetric, simp]" "cc = h (f1 x)" (fn ctxt => resolve_tac ctxt [@{thm hc} RS @{thm sym}]))
  in warnings_equal ["Light locale rule `Test7_Degeneracy.LH.foo_fused` [simp]: its left-hand side is led by locale parameter `h` which will be a schematic variable in the system registry. The system simplifier may not work as you expect. Consider stating it on a derived constant."] w; lthy' end\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    theorem_in lthy (Binding.name "foo_split") "[simp, symmetric]" "h (f2 x) = cc" (fn ctxt => resolve_tac ctxt @{thms hc}))
  in warnings_equal ["Light locale rule `Test7_Degeneracy.LH.foo_split` [simp]: its left-hand side is led by locale parameter `h` which will be a schematic variable in the system registry. The system simplifier may not work as you expect. Consider stating it on a derived constant."] w; lthy' end\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    theorem_in lthy Binding.empty "[simp]" "h (f3 x) = cc" (fn ctxt => resolve_tac ctxt @{thms hc}))
  in warnings_equal ["Light locale rule [simp]: its left-hand side is led by locale parameter `h` which will be a schematic variable in the system registry. The system simplifier may not work as you expect. Consider stating it on a derived constant."] w; lthy' end\<close>
lemma fooU: "h (f4 x) = cc" by (rule hc)
end

context LH begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () => declare_in lthy "LH.fooU" "[simp]")
  in warnings_equal ["Light locale rule [simp]: its left-hand side is led by locale parameter `h` which will be a schematic variable in the system registry. The system simplifier may not work as you expect. Consider stating it on a derived constant."] w; lthy' end\<close>
end

(*the stored LH.foo_split is the reversed statement, h and x schematic, under the predicate*)
ML \<open>
val _ = \<^assert> (Thm.prop_of @{thm LH.foo_split} aconv Logic.varify_global \<^prop>\<open>LH h \<Longrightarrow> cc = h (f2 x)\<close>);
val _ = \<^assert> (Thm.prop_of @{thm LH.foo_fused} aconv Logic.varify_global \<^prop>\<open>LH h \<Longrightarrow> h (f1 x) = cc\<close>);
\<close>

(* package-internal declarations are not checked (section 11, item (15)): fun's graph rules and
   inductive's introduction rules carry [Pure.intro?] (inductive.ML:1059), a Context_Rules
   declaration, although the rules contain h applied and the function variable applied *)
light_locale LN = fixes h :: "nat \<Rightarrow> nat"
begin
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    Function_Fun.add_fun_cmd [(Binding.name "ffun", NONE, NoSyn)]
      [((Binding.empty_atts, "ffun 0 = h 0"), [], []), ((Binding.empty_atts, "ffun (Suc k) = ffun k"), [], [])]
      Function_Fun.fun_config false lthy)
  in warnings_equal [] w; lthy' end\<close>
local_setup \<open>fn lthy =>
  let val (lthy', w) = with_warnings (fn () =>
    Inductive.add_inductive_cmd true false [(Binding.name "evn", SOME "nat \<Rightarrow> bool", NoSyn)] []
      [((Binding.empty_atts, "evn (h 0)"), [], []), ((Binding.empty_atts, "evn n \<Longrightarrow> evn (Suc n)"), [], [])]
      [] lthy |> #2)
  in warnings_equal [] w; lthy' end\<close>
end

end
