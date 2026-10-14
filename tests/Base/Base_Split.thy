(* Plan section 7 test 7: the fixture of the [split del] row (a global declaration, so it lives
   in its own theory of Light_Locale_Base; exactly one Light_Locale_Test leaf imports it).  The
   light block of LFsp (with a predicate) deletes the split rule of the test's own datatype tsp
   at theory level; the heavy twin's deletion of tsp2.split takes effect only where the locale is
   activated. *)
theory Base_Split
  imports "Light_Locale.Light_Locale"
begin

(*the test declares the datatypes' split rules [split] at theory level itself (the datatype package
  does not); the deletion goes by the case constant (splitter.ML:458-461)*)
datatype tsp = A | B
datatype tsp2 = A2 | B2
declare tsp.split [split] tsp2.split [split]

light_locale LFsp = fixes S :: "nat set" assumes "finite S"
locale Dsp = fixes S :: "nat set" assumes "finite S"

context LFsp begin
declare tsp.split [split del]
end

context Dsp begin
declare tsp2.split [split del]
end

end
