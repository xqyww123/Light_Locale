(* Plan section 7 test 4 (upgrade), the row "unfold_locales leaves exactly one goal" on the stand-in
   HD of the padic instance (plan section 11, implementation-period change (12)): the edge
   HB < d?: HD (Suc x) x reaches HD syntax-only inside context LF begin; there the predicate
   obligation of interpret HD (Suc x) x is closed by the witness of the syntax-only copy
   d.HD_axioms and only the reflexive defines equation Suc x == Suc x remains (show fails if no
   goal remained: the Plain defines note was wrongly replayed; qed fails if the predicate goal
   remained: the witness is missing).  The heavy twin's block closes both; the never-activated
   control leaves two goals.  The sublocale edge is persistent theory state, so this leaf owns it. *)
theory Test4_Block_Defines
  imports Test4_Fixture
begin

sublocale HB < d?: HD "Suc x" x by unfold_locales simp

light_locale LF = HB

locale D = HB

context LF begin
lemma True
proof -
  interpret HD "Suc x" x
  proof unfold_locales
    show "Suc x \<equiv> Suc x" by (rule reflexive)
  qed
  show True ..
qed
end

(* the heavy twin: zero goals; "apply unfold_locales done" because qed would also close a leftover
   reflexive equation and could not tell 0 goals from 1 *)
context D begin
lemma True
proof -
  interpret HD "Suc x" x apply unfold_locales done
  show True ..
qed
end

(* the row's own fixture: a light locale importing HD directly (the defined parameter eliminated
   by D20, the padic shape); its block leaves exactly the reflexive equation, the heavy twin of this
   shape leaves it too (the defined parameter stays a fixed variable there) and is no contrast *)
light_locale LFd = HD
context LFd begin
lemma True
proof -
  interpret HD "Suc y" y
  proof unfold_locales
    show "Suc y \<equiv> Suc y" by (rule reflexive)
  qed
  show True ..
qed
end

lemma True
proof -
  interpret HD "Suc t" t
  proof unfold_locales
    show "t = t" ..
    show "Suc t \<equiv> Suc t" by (rule reflexive)
  qed
  show True ..
qed

end
