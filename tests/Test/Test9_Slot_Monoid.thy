(* Plan section 7 test 9 (structure), plan 5294-5299: the slot is read when a block opens, not
   copied at declaration -- monoid's slot, written long after monoid, comm_before and ring were
   declared, reaches X (declared after), domain and ring (declared before), the reopened
   group_hom (the first group block's slot arrives first); LF and H5m keep UP S (the eliminated
   position's own value, not UP_cring's inherited cut f S); UP_cring itself stays empty (its
   names R, P survive).  Own leaf: it writes the slot of HOL-Algebra's monoid. *)
theory Test9_Slot_Monoid
  imports Test9_Fixtures
begin

locale comm_before = monoid

context monoid
begin
set_implicit_structure "f G"
end

locale X = comm_before G for G (structure)
locale H5m = LF + comm_monoid G for G

ML \<open>
open Test_Support;
val thy = \<^theory>;
fun opened name = Locale.init (loc thy name) thy;
fun second name text =
  let val ctxt = opened name in
    if implicit_is ctxt (reads ctxt text) then ()
    else error ("second layer of " ^ name ^ ": " ^ @{make_string} (Syntax_Trans.implicit_structure ctxt))
  end;
val _ = second "monoid" "f G";
val _ = second "X" "f G";
val _ = second "domain" "f R";
val _ = second "ring" "f R";
val _ = second "group_hom" "f G";
val _ = second "LF" "UP S";
val _ = second "H5m" "UP S";
val _ = \<^assert> (is_none (Syntax_Trans.implicit_structure (opened "UP_cring")));
\<close>

end
