(* The only theory of Light_Locale_Test_Serial (plan section 7, session graph): it imports test 6's
   fork-shape leaf of Light_Locale_Test by qualified name, so the same source file is processed
   again in this session's process with parallel_proofs = 0 (the HOL-Codegenerator_Test /
   HOL-Proofs way, HOL/ROOT:48-56, :374-382). *)
theory Serial_Wrapper
  imports "Light_Locale_Test.Test6_Fork"
begin

ML \<open>
  (* plan section 7, session graph: this session's name is set by build.ML:80 *)
  val _ = \<^assert> (Session.get_name () = "Light_Locale_Test_Serial");
\<close>

end
