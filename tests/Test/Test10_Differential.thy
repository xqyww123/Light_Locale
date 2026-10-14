(* Plan section 7 test 10 (sublocale from a light locale), the not-restated differential: the
   light edge sublocale LF <= c: C (x + 1) rewrites "x + 1 + 0 = x + 1" (the left-hand side occurs
   neither in the instance nor in an import term of C); an interpretation of C (x + 1) WITHOUT
   restating, once in the declaration block and once in a reopened block, gives the same theorem
   c.cl in both places, unrewritten; restating the rewrites gives the rewritten theorem (positive
   control); an edge without rewrites agrees between the block and the reopened block. *)
theory Test10_Differential
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

locale C = fixes v :: nat assumes cv: "v = v"
lemma (in C) cl: "v + 0 = v" by simp
ML \<open>structure Saved = Theory_Data (type T = thm list val empty = [] val merge = Thm.merge_thms)\<close>

light_locale LF = fixes x :: nat assumes "x = x"
begin
sublocale c: C "x + 1" rewrites "x + 1 + 0 = x + 1" by unfold_locales simp_all
interpretation i: C "x + 1" by unfold_locales simp
ML_val \<open>\<^assert> (Thm.prop_of @{thm i.cl} aconv \<^prop>\<open>x + 1 + 0 = x + 1\<close>)\<close>
local_setup \<open>Local_Theory.background_theory (Saved.map (cons @{thm i.cl}))\<close>
end

context LF begin
interpretation i: C "x + 1" by unfold_locales simp
ML_val \<open>
val _ = \<^assert> (Thm.eq_thm (@{thm i.cl}, hd (Saved.get \<^theory>)));
val _ = \<^assert> (Thm.prop_of @{thm i.cl} aconv \<^prop>\<open>x + 1 + 0 = x + 1\<close>);
\<close>
end

(* the positive control: restating the rewrites on the interpretation rewrites the theorem *)
light_locale LF2 = fixes x :: nat assumes "x = x"
begin
sublocale c: C "x + 1" rewrites "x + 1 + 0 = x + 1" by unfold_locales simp_all
interpretation r: C "x + 1" rewrites "x + 1 + 0 = x + 1" by unfold_locales simp_all
ML_val \<open>\<^assert> (Thm.prop_of @{thm r.cl} aconv \<^prop>\<open>x + 1 = x + 1\<close>)\<close>
end
context LF2 begin
interpretation r: C "x + 1" rewrites "x + 1 + 0 = x + 1" by unfold_locales simp_all
ML_val \<open>\<^assert> (Thm.prop_of @{thm r.cl} aconv \<^prop>\<open>x + 1 = x + 1\<close>)\<close>
end

(* without rewrites *)
light_locale LG = fixes y :: nat assumes "y = y"
begin
sublocale d: C "y + 2" by unfold_locales simp
interpretation j: C "y + 2" by unfold_locales simp
local_setup \<open>Local_Theory.background_theory (Saved.map (cons @{thm j.cl}))\<close>
end
context LG begin
interpretation j: C "y + 2" by unfold_locales simp
ML_val \<open>\<^assert> (Thm.eq_thm (@{thm j.cl}, hd (Saved.get \<^theory>)))\<close>
end

end
