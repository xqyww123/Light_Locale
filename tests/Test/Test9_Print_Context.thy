(* Plan section 7 test 9 (structure), plan 5311-5314: print_context (Proof_Context.debug on) --
   the structures line with the implicit structure first, then the variable structures; with no
   implicit structure the line is stock's, byte for byte and with the same markup (golden,
   recorded from the stock copy's context A: the text, and the markup tree of symbolic output);
   with neither layer there is no structures line. *)
theory Test9_Print_Context
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;
val golden = golden_line \<^theory> "structures.golden";
fun debug ctxt = Proof_Context.pretty_ctxt (Config.put Proof_Context.debug true ctxt);
fun structures_line ctxt = clean (Print_Mode.setmp [] Pretty.string_of (hd (debug ctxt)));
fun structures_markup ctxt =
  XML.string_of (XML.Elem (("line", []), YXML.parse_body (Pretty.symbolic_string_of (hd (debug ctxt)))));
\<close>

context LF
begin
ML_val \<open>\<^assert> (structures_line \<^context> = "structures: " ^ golden "UP_S")\<close>
end

context H'
begin
ML_val \<open>\<^assert> (structures_line \<^context> = "structures: " ^ golden "UP_S" ^ ", G")\<close>
end

context H
begin
ML_val \<open>
val _ = \<^assert> (structures_line \<^context> = golden "structures_A");
val _ = \<^assert> (structures_markup \<^context> = golden "structures_A_markup");
\<close>
end

(* neither layer: no structures block at all *)
ML \<open>
val _ = \<^assert> (not (exists (String.isPrefix "structures:" o clean o Print_Mode.setmp [] Pretty.string_of)
  (debug \<^context>)));
\<close>

end
