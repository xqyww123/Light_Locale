(* Plan section 7 test 9 (structure), plan 5300-5301: the slot of a fully instantiated import
   still arrives first -- Gm's slot f G, K3 = Gm X + Bt for X opens with f X. *)
theory Test9_Slot_Gm
  imports Test9_Fixtures
begin

context Gm
begin
set_implicit_structure "f G"
end

locale K3 = Gm X + Bt for X

ML \<open>
val ctxt = Locale.init (Test_Support.loc \<^theory> "K3") \<^theory>;
val _ = \<^assert> (Syntax_Trans.default_struct ctxt = SOME "T");
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "f X"));
\<close>

end
