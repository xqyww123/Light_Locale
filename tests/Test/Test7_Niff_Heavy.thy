(* The heavy twin of Test7_Niff (plan lines 4916-4918), in its own theory: in the heavy block DN,
   niff [iff] makes simp, auto and blast close Rc a S ==> False. *)
theory Test7_Niff_Heavy
  imports Test_Support
begin

consts Rc :: 'a
axiomatization where Rc_ax: "\<not> Rc x (n :: nat)"

locale DN = fixes S :: nat assumes "S = S"

context DN begin
lemma niff [iff]: "\<not> Rc x S" by (rule Rc_ax)
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by simp
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by auto
lemma "Rc (a :: 'q) S \<Longrightarrow> False" by blast
end

end
