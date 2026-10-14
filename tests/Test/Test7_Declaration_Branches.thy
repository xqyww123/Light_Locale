(* Plan section 7 test 7: the three branches of a declaration in a light block (section 3.3): a string table filled by declaration (block only), declaration (pervasive) (reaches the theory) and syntax_declaration (replayed from the record).  Inside the block all three are there; after end the theory has only "q"; a reopened context LF has "s" and "q" but not "p"; the heavy twin D has all three when reopened. *)
theory Test7_Declaration_Branches
  imports Test_Support "Light_Locale_Base.Light_Locale_Base"
begin

ML \<open>open Test_Support\<close>

ML \<open>structure Tab = Generic_Data (type T = string list val empty = [] fun merge (a, b) = a @ b)\<close>

context LF begin
declaration \<open>K (Tab.map (cons "p"))\<close>
declaration (pervasive) \<open>K (Tab.map (cons "q"))\<close>
syntax_declaration \<open>K (Tab.map (cons "s"))\<close>
ML_val \<open>\<^assert> (sort_strings (Tab.get (Context.Proof \<^context>)) = ["p", "q", "s"])\<close>
end

ML \<open>val _ = \<^assert> (Tab.get (Context.Theory \<^theory>) = ["q"])\<close>

context LF begin
ML_val \<open>\<^assert> (sort_strings (Tab.get (Context.Proof \<^context>)) = ["q", "s"])\<close>
end

context D begin
declaration \<open>K (Tab.map (cons "pD"))\<close>
declaration (pervasive) \<open>K (Tab.map (cons "qD"))\<close>
syntax_declaration \<open>K (Tab.map (cons "sD"))\<close>
end

context D begin
ML_val \<open>\<^assert> (subset (op =) (["pD", "qD", "sD"], Tab.get (Context.Proof \<^context>)))\<close>
end

end
