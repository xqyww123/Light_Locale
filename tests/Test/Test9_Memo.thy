(* Plan section 7 test 9 (structure), plan 5266-5267: the memo table of the summary -- a ladder
   of depth 30 declares within the session's timeout of 300 s (tests/ROOT: options [timeout];
   the session takes about a minute) and opens within 10 s (Timeout.apply below); without the
   table the walk is exponential already in the header route's imports_structure_state at
   declaration time. *)
theory Test9_Memo
  imports Test9_Fixtures
begin

locale L0 = fixes x :: 'a
locale L1 = a: L0 + b: L0
locale L2 = a: L1 + b: L1
locale L3 = a: L2 + b: L2
locale L4 = a: L3 + b: L3
locale L5 = a: L4 + b: L4
locale L6 = a: L5 + b: L5
locale L7 = a: L6 + b: L6
locale L8 = a: L7 + b: L7
locale L9 = a: L8 + b: L8
locale L10 = a: L9 + b: L9
locale L11 = a: L10 + b: L10
locale L12 = a: L11 + b: L11
locale L13 = a: L12 + b: L12
locale L14 = a: L13 + b: L13
locale L15 = a: L14 + b: L14
locale L16 = a: L15 + b: L15
locale L17 = a: L16 + b: L16
locale L18 = a: L17 + b: L17
locale L19 = a: L18 + b: L18
locale L20 = a: L19 + b: L19
locale L21 = a: L20 + b: L20
locale L22 = a: L21 + b: L21
locale L23 = a: L22 + b: L22
locale L24 = a: L23 + b: L23
locale L25 = a: L24 + b: L24
locale L26 = a: L25 + b: L25
locale L27 = a: L26 + b: L26
locale L28 = a: L27 + b: L27
locale L29 = a: L28 + b: L28
locale L30 = a: L29 + b: L29

context L30
begin
end

ML \<open>
val ctxt =
  Timeout.apply (Time.fromSeconds 10) (fn () => Locale.init (Test_Support.loc \<^theory> "L30") \<^theory>) ();
val _ = \<^assert> (is_none (Syntax_Trans.implicit_structure ctxt));
(*the header route's walk over two L29 imports, memoised, is as fast*)
val _ =
  Timeout.apply (Time.fromSeconds 10) (fn () =>
    \<^assert> (case Locale.imports_structure_state \<^theory> []
        [(Test_Support.loc \<^theory> "L29", [Locale.Inherited]),
         (Test_Support.loc \<^theory> "L29", [Locale.Inherited])] of
      Locale.Inherited_Structure => true | _ => false)) ();
\<close>

end
