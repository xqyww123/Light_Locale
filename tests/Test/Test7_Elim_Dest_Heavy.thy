(* The heavy twin of Test7_Elim_Dest (plan lines 4874-4889), in its own theory so that no light
   rule is registered: the groups that have heavy rows in the plan (Rc0 bad, Rc2 bad5, Rc3 bad6,
   Rc6 bad5', Rc7 fooI, Rc8 bad7, with the shared conclusion Sc) in the heavy block DE; the rules
   of Rc0, Rc2, Rc3, Rc6 and Rc7 each follow the control that their rows' goal is not closed before
   them, bad7 and the datatype's distinct rule have none (Rc8, TC and TD occur in no other rule)
   -- bad [dest] closes by blast; bad5 [elim] by blast and auto; bad6
   [elim] (ex falso) by blast and auto, no warning; apply safe with bad7 and with the datatype's
   distinct rule closes; blast closes the distinct rule's goal; the ".." forms of bad5' [elim?]
   and fooI [intro] with the chained h succeed. *)
theory Test7_Elim_Dest_Heavy
  imports Test_Support
begin

ML \<open>open Test_Support\<close>

(*row groups as in Test7_Elim_Dest: Rc0 bad, Rc2 bad5, Rc3 bad6, Rc6 bad5', Rc7 fooI, Rc8 bad7*)
consts Sc :: 'a  Rc0 :: 'a  Rc2 :: 'a  Rc3 :: 'a  Rc6 :: 'a  Rc7 :: 'a  Rc8 :: 'a
axiomatization where Sc_ax: "Sc x" and Rc3_ax: "Rc3 x (n :: nat) \<Longrightarrow> False"

ML \<open>fun after_safe ctxt goal = subgoals (run_apply ctxt [] "safe" goal)\<close>

locale DE = fixes S :: nat assumes "S = S"

context DE begin
lemma bad: "Rc0 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc0 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
declare bad [dest]
lemma "Rc0 (a :: 'q) S \<Longrightarrow> Sc a" by blast
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc2 (a :: 'q) S \<Longrightarrow> Sc a\<close>) andalso not (by_auto \<^context> \<^prop>\<open>Rc2 (a :: 'q) S \<Longrightarrow> Sc a\<close>))\<close>
lemma bad5 [elim]: "Rc2 x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma "Rc2 (a :: 'q) S \<Longrightarrow> Sc a" by blast
lemma "Rc2 (a :: 'q) S \<Longrightarrow> Sc a" by auto
ML_val \<open>\<^assert> (not (by_blast \<^context> \<^prop>\<open>Rc3 (a :: 'q) S \<Longrightarrow> Q\<close>) andalso not (by_auto \<^context> \<^prop>\<open>Rc3 (a :: 'q) S \<Longrightarrow> Q\<close>))\<close>
lemma bad6 [elim]: "Rc3 x S \<Longrightarrow> R" by (drule Rc3_ax) simp
ML_val \<open>\<^assert> (blast_warns \<^context> "Rc3 (a :: 'q) S \<Longrightarrow> Q" = (true, false))\<close>
lemma "Rc3 (a :: 'q) S \<Longrightarrow> Q" by auto
lemma bad7 [elim!]: "Rc8 x \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
datatype trd = TC | TD
ML_val \<open>
val _ = \<^assert> (after_safe \<^context> "Rc8 (a :: 'q) \<Longrightarrow> Sc a" = 0);
val _ = \<^assert> (after_safe \<^context> "TC = TD \<Longrightarrow> P" = 0);
val _ = \<^assert> (blast_warns \<^context> "TC = TD \<Longrightarrow> P" = (true, false));
\<close>
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc6 a S";
val _ = \<^assert> (not (by_method ctxt [h] "standard" "Sc a"));
\<close>
lemma bad5' [elim?]: "Rc6 x S \<Longrightarrow> (Sc x \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: Sc_ax)
lemma assumes h: "Rc6 (a :: 'q) S" shows "Sc a" using h ..
ML_val \<open>
val (h, ctxt) = assume_in \<^context> [("a", \<^typ>\<open>'q\<close>)] "h" "Rc7 a S";
val _ = \<^assert> (not (by_method ctxt [h] "standard" "Sc a"));
\<close>
lemma fooI [intro]: "Rc7 x S \<Longrightarrow> Sc x" by (rule Sc_ax)
lemma assumes h: "Rc7 (a :: 'q) S" shows "Sc a" using h ..
end

end
