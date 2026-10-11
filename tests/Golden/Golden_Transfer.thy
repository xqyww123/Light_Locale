(* Plan section 7 test 1: the whole Transfer table (transfer rules and Domainp rules) of Main --
   only Main, because a fixture session's block-level datatypes would add entries of their own. *)
theory Golden_Transfer
  imports Main
begin

ML_file "golden.ML"

ML \<open>
let
  val ctxt = \<^context>;
  fun entries kind get = map (pair kind) (get ctxt);
  val table =
    entries "transfer_raw" Transfer.get_transfer_raw @ entries "relator_domain" Transfer.get_relator_domain
    |> map (fn (kind, th) => (kind, Golden.thms_dump [(kind, th)]))
    |> sort (string_ord o apply2 #2) |> map #2 |> implode;
in Golden.check \<^theory> "transfer_table.golden" table end;
\<close>

end
