(* ========================================================================== *)
(* Exact theorem-name bridge for the historical Flyspeck Azure sources.      *)
(*                                                                            *)
(* The Azure sources qualified these five real square-root theorems through  *)
(* their old Vectors module.  Candle's current HOL Light base exports the     *)
(* identical theorem values at top level.  This module restores only the     *)
(* names used by the authenticated definitions.hl support source; it creates  *)
(* no theorem, changes no statement, and introduces no axiom.                 *)
(* ========================================================================== *)

module Vectors = struct
  let SQRT_LE_0 = SQRT_LE_0;;
  let SQRT_POW_2 = SQRT_POW_2;;
  let SQRT_MUL = SQRT_MUL;;
  let POW_2_SQRT_ABS = POW_2_SQRT_ABS;;
  let SQRT_MONO_LT_EQ = SQRT_MONO_LT_EQ;;
end;;

if hyp Vectors.SQRT_LE_0 <> [] ||
   hyp Vectors.SQRT_POW_2 <> [] ||
   hyp Vectors.SQRT_MUL <> [] ||
   hyp Vectors.POW_2_SQRT_ABS <> [] ||
   hyp Vectors.SQRT_MONO_LT_EQ <> [] then
  failwith "historical Vectors theorem bridge assumptions mismatch"
else
  print_endline "CANDLE_FLYSPECK_VECTORS_COMPATIBILITY_OK";;
