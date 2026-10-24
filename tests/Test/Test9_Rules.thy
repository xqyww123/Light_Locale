(* Plan section 7 test 9 (structure): every rule of the computation of the implicit structure
   (plan decision 16 (c); rows at plan 5113-5170) -- the first layer (the head of the variable
   structures) and the second layer (the implicit structure) of every locale when opened, with the
   heavy twins; the show_structs guard (plan 5109-5110).  Nothing here writes a slot. *)
theory Test9_Rules
  imports Test9_Fixtures
begin

ML \<open>
open Test_Support;

(*the two layers of the locale's block (of the theory current when called, not of this block's):
  the expected second layer is read in that block*)
fun check name first second =
  let
    val thy = Context.the_global_context ();
    val ctxt = Locale.init (loc thy name) thy;
    val _ =
      if Syntax_Trans.default_struct ctxt = first then ()
      else error ("first layer of " ^ name ^ ": " ^ @{make_string} (Syntax_Trans.default_struct ctxt));
    val _ =
      (case second of
        NONE =>
          if is_none (Syntax_Trans.implicit_structure ctxt) then ()
          else error ("second layer of " ^ name ^ " is not empty")
      | SOME text =>
          if implicit_is ctxt (reads ctxt text) then ()
          else error ("second layer of " ^ name ^ ": " ^
            @{make_string} (Syntax_Trans.implicit_structure ctxt)));
  in ctxt end;

fun bare_is ctxt text = \<^assert> (bare_denotes ctxt text);
\<close>


subsection \<open>All heavy: the first layer is stock's, the second layer empty (plan 5124-5134)\<close>

locale inherit = monoid
locale renamed = monoid G for G
locale redeclared = monoid G for G (structure)
locale two = fixes G :: "('a, 'b) monoid_scheme" (structure) and H :: "('a, 'b) monoid_scheme" (structure)
locale D2 = two X + Bt for X
locale K = monoid "f R" for R :: "('a, 'b) monoid_scheme" (structure)
locale SA = fixes a :: "('a, 'b) monoid_scheme" (structure)
locale SB = fixes b :: "('a, 'b) monoid_scheme" (structure)
locale SC = fixes c :: "('a, 'b) monoid_scheme" (structure)
locale SL = SA q + SB p for p :: "('a, 'b) monoid_scheme" (structure) and q (structure)
locale SD = fixes G :: "('a, 'b) monoid_scheme" (structure) and H :: "('a, 'b) monoid_scheme" (structure)
sublocale SD \<subseteq> SC H by unfold_locales
locale D1 = UPm R for R (structure)
locale D1s = UPm S for S (structure)
locale Kp = G?: Gm G + D1s for G (structure)
locale Kx = G?: Gm X + D1s for X (structure)
locale Kb = Gm G + D1s + Bm
locale KX = Gm X + Bt for X
locale Rg = Gm R + Bt R for R (structure)
locale Da = fixes T :: "('a, 'b) monoid_scheme" (structure) and Q :: "('a, 'b) monoid_scheme"
sublocale Da \<subseteq> UPm Q "f Q" by simp

ML \<open>
val ctxt = check "inherit" (SOME "G") NONE;
val _ = bare_is ctxt "G";
val ctxt = check "renamed" NONE NONE;
val _ = fails_with "Illegal reference to implicit structure" (fn () => reads ctxt "x \<otimes> y");
val _ = check "redeclared" (SOME "G") NONE;
val _ = check "two" (SOME "G") NONE;
val _ = check "D2" (SOME "H") NONE;
val _ = check "K" (SOME "R") NONE;
val _ = check "SL" (SOME "p") NONE;
val _ = check "SD" (SOME "G") NONE;
val _ = check "D1" (SOME "P") NONE;
val _ = check "D1s" (SOME "P") NONE;
val _ = check "Kp" (SOME "P") NONE;
val _ = check "Kx" (SOME "P") NONE;
val _ = check "Kb" (SOME "P") NONE;
val _ = check "KX" (SOME "T") NONE;
val _ = check "Rg" (SOME "R") NONE;
val _ = check "Da" (SOME "T") NONE;
\<close>

(* the sublocale edge does not take part: Child's assumption is on G (plan 5132-5134) *)
locale Mid = fixes G :: "('a, 'b) monoid_scheme" (structure) and R' :: "('c, 'd) ring_scheme"
sublocale Mid \<subseteq> UP R' "UP R'" by simp
locale Child = Mid + fixes x y assumes c: "x \<otimes> y = y \<otimes> x"
ML \<open>
val ctxt = check "Child" (SOME "G") NONE;
val [Element.Assumes [(_, [(asm, _)])]] =
  filter (fn Element.Assumes _ => true | _ => false) (Locale.hyp_spec_of \<^theory> (loc \<^theory> "Child"));
val _ = \<^assert> (asm aconv Syntax.read_prop ctxt "x \<otimes>\<^bsub>G\<^esub> y = y \<otimes>\<^bsub>G\<^esub> x");
(*byte for byte what stock records (golden, rendered without the printer)*)
val _ = \<^assert> (ML_Syntax.print_term asm = golden_line \<^theory> "structures.golden" "Child_assumption");
\<close>


subsection \<open>The gate fixture and the same-name instantiations (plan 5135-5138)\<close>

locale Kp' = G?: group G + LF for G (structure)
locale Kb' = A G + LF + B

ML \<open>
val ctxt = check "LF" NONE (SOME "UP S");
val _ = bare_is ctxt "UP S";
val _ = check "D" (SOME "P") NONE;
val ctxt = check "LFr" NONE (SOME "UP R");
val _ = bare_is ctxt "UP R";
val _ = check "LFr2" (SOME "R") NONE;
val _ = check "Kp'" (SOME "G") (SOME "UP S");
val _ = check "Kb'" (SOME "G") (SOME "UP S");
\<close>


subsection \<open>A surviving head instantiated away (plan 5139-5151)\<close>

locale M1n = LU S for S
locale M1w = LU where R = S for S (structure)
locale M2 = LU2 S for S (structure)
locale M3 = A?: LU G + B?: Gm H for G (structure) and H (structure)
locale N = LU
locale N2 = N
locale M4d = N2 S for S (structure)
locale M5 = Gm X + LU X for X (structure)
locale K2 = LU X + Bt for X
locale DD = LU + UPm
locale DD2 = LU S + UPm S for S (structure)
light_locale L2 = LU S for S
light_locale L3 = L2 where S = T for T
light_locale LUr = UPr
locale Mr = LUr where R = S for S (structure)
light_locale LC = UPc
locale MC = LC S for S (structure)
light_locale LC2 = UPc2
locale MC2 = LC2 S for S (structure)

ML \<open>
val _ = check "LU" (SOME "R") NONE;
val _ = check "M1" (SOME "S") (SOME "f S");
val _ = check "M1n" NONE (SOME "f S");
val _ = check "M1w" (SOME "S") (SOME "f S");
val _ = check "LU2" (SOME "R") NONE;
val _ = check "M2" (SOME "T") (SOME "f S");
val _ = check "M3" (SOME "G") (SOME "f G");
val _ = check "M4d" (SOME "S") (SOME "f S");
val _ = check "M5" (SOME "X") (SOME "f X");
val _ = check "K2" (SOME "T") (SOME "f X");
val _ = check "DD" (SOME "R") NONE;
val _ = check "DD2" (SOME "P") (SOME "f S");
val _ = check "L3" NONE (SOME "f T");
val _ = check "LUr" (SOME "R") (SOME "f R");
val _ = check "Mr" (SOME "S") (SOME "f S");
val _ = check "LC" (SOME "R") NONE;
val _ = check "MC" (SOME "S") (SOME "f S");
val _ = check "MC2" (SOME "S") (SOME "f (f S)");
\<close>


subsection \<open>Header order (plan 5152-5158)\<close>

locale H2 = H' + fixes T :: "('a, 'b) monoid_scheme" (structure)
locale Hq = A q + LF for p :: "('a, 'b) monoid_scheme" (structure) and q (structure)
locale Bb = fixes b :: "('a, 'b) monoid_scheme" (structure)
locale Hb = A b + LF + Bb
locale Hg = Gm + LF
locale H3 = Hg X for X
light_locale LF3' = H'
locale H3' = LF3'
locale H4 = LF T for T
locale H5 = H4 U for U + assumes "x \<otimes> y = y \<otimes> x"

ML \<open>
val ctxt = check "H" (SOME "G") NONE;
val _ = bare_is ctxt "G";
val ctxt = check "H'" (SOME "G") (SOME "UP S");
val _ = bare_is ctxt "UP S";
val _ = check "H2" (SOME "G") (SOME "UP S");
val _ = check "Hq" (SOME "p") (SOME "UP S");
val _ = check "Hb" (SOME "b") (SOME "UP S");
val _ = check "H3" NONE (SOME "UP S");
val _ = check "LF3'" (SOME "G") (SOME "UP S");
val _ = check "H3'" (SOME "G") (SOME "UP S");
val _ = check "H4" NONE (SOME "UP T");
val ctxt = check "H5" NONE (SOME "UP U");
val [Element.Assumes [(_, [(asm, _)])]] =
  filter (fn Element.Assumes _ => true | _ => false) (Locale.hyp_spec_of \<^theory> (loc \<^theory> "H5"));
val _ = \<^assert> (asm aconv Syntax.read_prop ctxt "\<And>x y. x \<otimes>\<^bsub>UP U\<^esub> y = y \<otimes>\<^bsub>UP U\<^esub> x");
\<close>


subsection \<open>The same-name corner and the headers without a heavy twin (plan 5159-5167)\<close>

locale M6 = LU S + Pm for S
locale M6x = LU S + Gm + Pm for S
locale M6r = Pm + LU S for S
locale Y = M6 Q S for Q (structure) and S (structure)
locale Y3 = M6 Q S for Q and S (structure)
locale M6xq = M6x where P = Q for Q
light_locale M11 = UPm where R = S and P = "f S" for S
locale GH = A: LU G + B: LU H for G (structure) and H (structure)

ML \<open>
val _ = check "M6" (SOME "P") (SOME "f S");
val _ = check "M6x" (SOME "G") (SOME "f S");
val _ = check "M6r" (SOME "P") NONE;
val _ = check "Y" (SOME "Q") (SOME "f S");
val _ = check "Y3" (SOME "S") (SOME "f S");
val _ = check "M6xq" (SOME "G") (SOME "f S");
val _ = check "M11" NONE (SOME "f S");
val _ = check "GH" (SOME "G") (SOME "f G");
\<close>


subsection \<open>The show_structs guard (plan 5109-5110): every index explicit when it is on\<close>

ML \<open>
fun with_structs on name = Config.put show_structs on (Locale.init (loc \<^theory> name) \<^theory>);
val golden = golden_line \<^theory> "structures.golden";
val _ = prints_as (with_structs true "LFr") "x \<otimes> y" (golden "otimes_UP_R");
val _ = prints_as (with_structs true "M1") "x \<otimes> y" (golden "otimes_f_S");
val _ = prints_as (with_structs true "H'") "x \<otimes> y" (golden "otimes_UP_S");
val _ = List.app (fn name => prints_as (with_structs false name) "x \<otimes> y" "x \<otimes> y")
  ["LFr", "M1", "H'"];
\<close>


subsection \<open>The heavy twins of the light rows (plan 5114): stock's first layer, no second\<close>

locale DFr = UP_cring R for R (structure)
locale DFr2 = UP_cring
locale DKp' = G?: group G + D for G (structure)
locale DKb' = A G + D + B
locale DM1n = UPm S for S
locale DM1w = UPm where R = S for S (structure)
locale DLU2 = UPm2
locale DM2 = UPm2 S for S (structure)
locale DM3 = A?: UPm G + B?: Gm H for G (structure) and H (structure)
locale DN = UPm
locale DN2 = DN
locale DM4d = DN2 S for S (structure)
locale DM5 = Gm X + UPm X for X (structure)
locale DK2 = UPm X + Bt for X
locale DDD = DN + UPm
locale DDD2 = DN S + UPm S for S (structure)
locale DL2 = UPm S for S (structure)
locale DL3 = DL2 where S = T for T (structure)
locale DUr = UPr
locale DMr = DUr where R = S for S (structure)
locale DLC = UPc
locale DMC = DLC S for S (structure)
locale DLC2 = UPc2
locale DMC2 = DLC2 S for S (structure)
locale DH = A + D
locale DH' = D + A
locale DH2 = DH' + fixes T :: "('a, 'b) monoid_scheme" (structure)
locale DHq = A q + D for p :: "('a, 'b) monoid_scheme" (structure) and q (structure)
locale DHb = A b + D + Bb
locale DHg = Gm + D
locale DH3 = DHg X for X
locale DF3' = DH'
locale DH3' = DF3'
locale DH4 = D where S = T for T
locale DH5 = DH4 where T = U for U + assumes "x \<otimes> y = y \<otimes> x"
locale DM6 = UPm S + Pm for S
locale DM6x = UPm S + Gm + Pm for S
locale DM6r = Pm + UPm S for S
locale DY = DM6 Q S for Q (structure) and S (structure)
locale DY3 = DM6 Q S for Q and S (structure)
locale DM6xq = DM6x where P = Q for Q

ML \<open>
val _ = List.app (fn (name, head) => (check name (SOME head) NONE; ()))
  [("DFr", "P"), ("DFr2", "R"), ("DKp'", "P"), ("DKb'", "P"), ("DN", "R"), ("DM1n", "P"), ("DM1w", "P"),
   ("DLU2", "R"), ("DM2", "P"), ("DM3", "P"), ("DM4d", "P"), ("DM5", "P"), ("DK2", "P"), ("DDD", "R"),
   ("DDD2", "P"), ("DL3", "P"), ("DUr", "P"), ("DMr", "P"), ("DLC", "R"), ("DMC", "P"), ("DLC2", "R"),
   ("DMC2", "Q"), ("DH", "G"), ("DH'", "P"), ("DH2", "P"), ("DHq", "P"), ("DHb", "P"), ("DH3", "P"),
   ("DF3'", "P"), ("DH3'", "P"), ("DH4", "P"), ("DH5", "P"), ("DM6", "P"), ("DM6x", "P"), ("DM6r", "P"),
   ("DY", "Q"), ("DY3", "S"), ("DM6xq", "G")];
(*the twins' definitions the plan names (5159-5163: the merged P is defined as f S, Y's renamed
  head Q as f S); DM1n's P == f S is an addition beyond the plan*)
fun defined_as name fact text =
  let val ctxt = Locale.init (loc \<^theory> name) \<^theory>
  in \<^assert> (Thm.prop_of (Proof_Context.get_thm ctxt fact) aconv Syntax.read_prop ctxt text) end;
val _ = defined_as "DM1n" "P_def" "P \<equiv> f S";
val _ = defined_as "DM6x" "P_def" "P \<equiv> f S";
val _ = defined_as "DM6r" "P_def" "P \<equiv> f S";
val _ = defined_as "DY" "P_def" "Q \<equiv> f S";
val _ = defined_as "DY3" "P_def" "Q \<equiv> f S";
\<close>


subsection \<open>sublocale does not take part (plan 5168-5170)\<close>

sublocale M1 \<subseteq> Gm "f (f S)" by unfold_locales
locale HD = fixes q :: 'q and Z :: "('a, 'b) ring_scheme" (structure) defines "Z \<equiv> tmk q"
sublocale HD < U?: UP Z "UP Z" by simp
light_locale LD = HD

ML \<open>
val _ = check "M1" (SOME "S") (SOME "f S");
val _ = check "LD" NONE (SOME "tmk q");
val _ = check "HD" (SOME "Z") NONE;
\<close>

end
