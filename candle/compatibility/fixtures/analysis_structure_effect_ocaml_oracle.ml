type analysis_theorem = Analysis_theorem of string;;

let original_trace = ref [];;
let original_theorem name =
  original_trace := name::!original_trace;
  Analysis_theorem name;;
let original_unit name = original_trace := name::!original_trace;;
module Original = struct
  original_theorem "REAL_LE_SQUARE_ABS";;
  original_theorem "REAL_ABS_REFL";;
  original_unit "prioritize_num";;
  original_unit "POWER";;
  original_unit "in_dart_of_loop";;
  original_unit "iso";;
  original_unit "translation-short";;
  original_unit "linear-short";;
  original_unit "translation-multiline";;
  original_unit "linear-multiline";;
  let exported = true;;
end;;

let normalized_trace = ref [];;
let normalized_theorem name =
  normalized_trace := name::!normalized_trace;
  Analysis_theorem name;;
let normalized_unit name = normalized_trace := name::!normalized_trace;;
module Normalized = struct
  let _ = normalized_theorem "REAL_LE_SQUARE_ABS";;
  let _ = normalized_theorem "REAL_ABS_REFL";;
  let _ = normalized_unit "prioritize_num";;
  let _ = normalized_unit "POWER";;
  let _ = normalized_unit "in_dart_of_loop";;
  let _ = normalized_unit "iso";;
  let _ = normalized_unit "translation-short";;
  let _ = normalized_unit "linear-short";;
  let _ = normalized_unit "translation-multiline";;
  let _ = normalized_unit "linear-multiline";;
  let exported = true;;
end;;

let () =
  if !normalized_trace = !original_trace && Original.exported &&
     Normalized.exported then
    print_endline "ANALYSIS_STRUCTURE_EFFECT_OCAML_ORACLE_OK"
  else failwith "analysis structure-effect OCaml oracle failed";;
