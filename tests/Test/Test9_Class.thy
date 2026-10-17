(* Plan section 7 test 9 (structure), plan 5171-5178: classes take part only through the slot.
   The three commands in this order and nothing else in this leaf: the class, its slot written
   from context C, the subclass -- whose superclass edge is all Written, so the cut carries over.
   The class parameter prints as the class constant, and so does the stored value put through
   the uncheck stages for the comparison: the index is elided (section 11 (39)). *)
theory Test9_Class
  imports Test9_Fixtures
begin

class C = fixes G :: "'a monoid"

context C
begin
set_implicit_structure G
end

class C1 = C + assumes c1: "\<And>x y. x \<otimes> y = y \<otimes> x"

context C
begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "G"));
val _ = \<^assert> (is_none (Syntax_Trans.default_struct ctxt));
\<close>
end

context C1
begin
ML_val \<open>
val ctxt = \<^context>;
val _ = \<^assert> (Test_Support.implicit_is ctxt (Test_Support.reads ctxt "G"));
val _ = Test_Support.prints_as ctxt "x \<otimes>\<^bsub>G\<^esub> y" "x \<otimes> y";
val _ = \<^assert> (Test_Support.round_trips ctxt (Test_Support.reads ctxt "x \<otimes>\<^bsub>G\<^esub> y"));
val _ = \<^assert> (Test_Support.bare_denotes ctxt "G");
\<close>
end

end
