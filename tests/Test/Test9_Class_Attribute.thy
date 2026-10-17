(* Plan section 7 test 9 (structure), the class header row with attributes (REV15-8, section 11
   (39)): as Test9_Class, the three commands in this order and nothing else -- the class, its
   slot written from context Cat, the subclass whose assumes carries a term parameter and a
   string parameter; both read \<one> on G, the string one through the class declaration's second
   evaluation.  A class has no heavy twin (a class parameter cannot be (structure)); the
   comparison drops the types, since the type variable names of that evaluation are not pinned. *)
theory Test9_Class_Attribute
  imports Test9_Fixtures
begin

class Cat = fixes G :: "'a monoid"

context Cat
begin
set_implicit_structure G
end

class Cat1 = Cat +
  assumes c1 [t9_premise "\<one>", THEN t9_premise_rule[where x = "\<one>"]]: "\<And>x. x \<otimes> \<one> = x"

context Cat1
begin
ML_val \<open>
val ctxt = \<^context>;
val expected = Syntax.read_prop ctxt "\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<^esub>";
val prems = Thm.prems_of @{thm c1};
val _ = \<^assert> (length prems = 2 andalso forall (fn p => Term.aconv_untyped (p, expected)) prems);
\<close>
end

end
