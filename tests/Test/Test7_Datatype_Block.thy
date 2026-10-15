(* Plan section 7 test 7: a datatype and a codatatype in the predicate block declare with the default plugins, and the code plugin's equal instance is not run on the theory (ctr_sugar_code.ML:134-135): Sorts.has_instance for class equal is false after end, for the heavy twin as well; a fun recursive over the block datatype (pattern equations and a case) and a primrec succeed in the declaration block. *)
theory Test7_Datatype_Block
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

context LF begin
datatype tr = Leaf | Node tr tr
codatatype str = SCons nat str
end

context D begin
datatype trd = LeafD | NodeD trd trd
codatatype strd = SConsD nat strd
end

ML \<open>
(*the type names are compile-checked antiquotations: a misspelt name would make has_instance
  false for the wrong reason*)
fun has_equal tyco = Sorts.has_instance (Sign.classes_of \<^theory>) tyco [\<^class>\<open>equal\<close>];
val _ = \<^assert> (not (has_equal \<^type_name>\<open>LF.tr\<close>));
val _ = \<^assert> (not (has_equal \<^type_name>\<open>LF.str\<close>));
val _ = \<^assert> (not (has_equal \<^type_name>\<open>D.trd\<close>));
val _ = \<^assert> (not (has_equal \<^type_name>\<open>D.strd\<close>));
\<close>

light_locale LFt = fixes S :: "nat set" assumes "finite S"
begin
datatype tr2 = Leaf2 | Node2 tr2 tr2
fun size2 :: "tr2 \<Rightarrow> nat" where
  "size2 Leaf2 = 0"
| "size2 (Node2 l r) = size2 l + size2 r + 1"
fun size3 :: "tr2 \<Rightarrow> nat" where
  "size3 t = (case t of Leaf2 \<Rightarrow> 0 | Node2 l r \<Rightarrow> size3 l + size3 r + 1)"
primrec size4 :: "tr2 \<Rightarrow> nat" where
  "size4 Leaf2 = 0"
| "size4 (Node2 l r) = size4 l + size4 r + 1"
end

end
