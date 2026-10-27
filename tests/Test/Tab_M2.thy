(* Plan section 7 test 12, the merge group (A10): both parents' entries after the merge, imports in
   the order Tab_B Tab_A. *)
theory Tab_M2
  imports Tab_B Tab_A
begin

ML \<open>
Test_Support.check_rows
 [("LFs {}", fn () =>
    Test_Support.retrieves_only \<^context> \<^prop>\<open>LFs ({}::nat set)\<close> @{thm I.LFs_axioms}),
  ("LFs {0}", fn () =>
    Test_Support.retrieves_only \<^context> \<^prop>\<open>LFs {0::nat}\<close> @{thm J.LFs_axioms})]
\<close>

end
