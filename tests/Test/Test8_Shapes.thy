(* Plan section 7 test 8 (declaration shapes), the gate clause on a test-internal heavy locale with a
   defines parameter (Pdef in place of padic_integers): the five spellings give the same declaration;
   another name or a different term at the defined position gives the section-6 message verbatim;
   a compatible type annotation is accepted; a dummy at a non-eliminated position gives stock's
   "Illegal dummy pattern(s)"; a conflicting annotation gives stock's type error ("Type unification
   failed", type_infer_context.ML), not the message. *)
theory Test8_Shapes
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

consts pint :: "nat \<Rightarrow> nat set"
locale Pdef = fixes Zp :: "nat set" and p :: nat defines "Zp \<equiv> pint p" assumes fin: "finite Zp"

light_locale L1 = Pdef _ p for p
light_locale L2 = Pdef "pint p" p for p
light_locale L3 = Pdef
light_locale L4 = Pdef where Zp = _
light_locale L5 = Pdef where Zp = "pint p"
light_locale L6 = Pdef "(pint p :: _)" p for p
light_locale L7 = Pdef "(pint p :: nat set)" p for p

ML \<open>
val thy = \<^theory>;
val ls = map (loc thy) ["L1", "L2", "L3", "L4", "L5", "L6", "L7"];
val _ = \<^assert> (forall (fn l => params thy l = [("p", \<^typ>\<open>nat\<close>, true)]) ls);
val _ = \<^assert> (forall (fn l => null (#2 (Locale.specification_of thy l))) ls);
val _ = \<^assert> (forall (fn l =>
  (case #1 (Locale.specification_of thy l) of
    SOME t => (case Term.strip_comb (HOLogic.dest_Trueprop t) of (Const (c, _), args) => c = l andalso args = [\<^term>\<open>p::nat\<close>] | _ => false)
  | NONE => false)) ls);
(*the recorded instance of Zp is the unfolded term*)
val _ = \<^assert> (forall (fn l => instances thy "Pdef" l = [\<^term>\<open>pint p\<close>, \<^term>\<open>p::nat\<close>]) ls);
\<close>

ML \<open>
val msg = defined_as "1st" "Zp" "Pdef" "pint p";
val _ = fails_with msg (light \<^theory> "LX = Pdef Zp p for p");
val _ = fails_with msg (light \<^theory> "LX = Pdef where Zp = Zp");
val _ = fails_with msg (light \<^theory> "LX = Pdef where Zp = \"pint q\" for q");
val _ = fails_prefix "Illegal dummy pattern(s) in term" (light \<^theory> "LX = Pdef where p = _");
(*a conflicting annotation: stock's type error, not the section-6 message*)
val _ = fails_prefix "Type unification failed" (light \<^theory> "LX = Pdef \"(pint p :: nat)\" p for p");
\<close>

end
