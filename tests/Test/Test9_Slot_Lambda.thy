(* Plan section 7 test 9 (structure), plan 5245-5247 and 5257-5258: a slot holding a term with a
   binder reaches a child declared afterwards with the same type as the twin block's operator;
   and after the slot of LFl is set to S, the reopened block's bare operator denotes S (the type
   rewrite on a re-set value is observable in Test9_Set, where the types differ; here every value
   has the cut's type).  One leaf for both rows: they are one slot-writing scenario (plan
   3825-3831), the second row reads only the write before it.  Fixtures UPl/LFl/Dl are in
   Test9_Fixtures. *)
theory Test9_Slot_Lambda
  imports Test9_Fixtures
begin

ML \<open>open Test_Support\<close>

context LFl
begin
set_implicit_structure "S\<lparr>mult := \<lambda>x y. y\<rparr>"
end

locale Hl = LFl + fixes z :: 'a
locale DHl = Dl + fixes z :: 'a

ML \<open>
val thy = \<^theory>;
val ctxt = Locale.init (loc thy "Hl") thy;
val _ = \<^assert> (implicit_is ctxt (reads ctxt "S\<lparr>mult := \<lambda>x y. y\<rparr>"));
val _ = \<^assert> (bare_denotes ctxt "S\<lparr>mult := \<lambda>x y. y\<rparr>");
(*the operator's type is that of the twin block's operator after elimination (the twin's M,
  same header text; the same shape as Test9_Header's rows, plan 5245-5247)*)
val _ = \<^assert> (fastype_of (reads ctxt "x \<otimes> y") =
  fastype_of (after_elimination thy "DHl" ["M"] (reads (Locale.init (loc thy "DHl") thy) "x \<otimes> y")));
\<close>

context LFl
begin
set_implicit_structure "S"
end

context LFl
begin
ML_val \<open>
val ctxt = \<^context>;
val t = reads ctxt "x \<otimes> y";
val _ = \<^assert> (t aconv reads ctxt "x \<otimes>\<^bsub>S\<^esub> y");
val _ = \<^assert> (fastype_of t = fastype_of (reads ctxt "x \<otimes>\<^bsub>S\<^esub> y"));
\<close>
end

end
