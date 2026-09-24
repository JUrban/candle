(* ========================================================================== *)
(* Exact theorem-name bridge for the historical Flyspeck Azure sources.      *)
(*                                                                            *)
(* The Azure sources qualified seven real-analysis theorems through their old *)
(* Vectors and Transcendentals modules.  Candle's current HOL Light base       *)
(* exports the identical theorem values at top level.  These modules restore  *)
(* the complete qualified-name inventory of the authenticated definitions.hl  *)
(* support source; they create no theorem, change no statement, and introduce *)
(* no axiom.                                                                   *)
(* ========================================================================== *)

module Vectors = struct
  let SQRT_LE_0 = SQRT_LE_0;;
  let SQRT_POW_2 = SQRT_POW_2;;
  let SQRT_MUL = SQRT_MUL;;
  let POW_2_SQRT_ABS = POW_2_SQRT_ABS;;
  let SQRT_MONO_LT_EQ = SQRT_MONO_LT_EQ;;
end;;

module Transcendentals = struct
  let ACS_ATN = ACS_ATN;;
  let ATN_NEG = ATN_NEG;;
end;;

if hyp Vectors.SQRT_LE_0 <> [] ||
   hyp Vectors.SQRT_POW_2 <> [] ||
   hyp Vectors.SQRT_MUL <> [] ||
   hyp Vectors.POW_2_SQRT_ABS <> [] ||
   hyp Vectors.SQRT_MONO_LT_EQ <> [] ||
   hyp Transcendentals.ACS_ATN <> [] ||
   hyp Transcendentals.ATN_NEG <> [] then
  failwith "historical Azure theorem bridge assumptions mismatch"
else
  print_endline "CANDLE_FLYSPECK_AZURE_THEOREM_COMPATIBILITY_OK";;
