(* Plan section 7 test 12, the merge group (A10): both parents' entries after the merge, imports in
   the order Tab_A Tab_B. *)
theory Tab_M1
  imports Tab_A Tab_B
begin

ML \<open>
Test_Support.check_rows
 [("LFs {}", fn () =>
    Test_Support.retrieves_only \<^context> \<^prop>\<open>LFs ({}::nat set)\<close> @{thm I.LFs_axioms}),
  ("LFs {0}", fn () =>
    Test_Support.retrieves_only \<^context> \<^prop>\<open>LFs {0::nat}\<close> @{thm J.LFs_axioms})]
\<close>

end
