type candle_analysis_theorem = Candle_analysis_theorem of string;;

let candle_analysis_theorem_trace = ref ([]:string list);;
let candle_analysis_theorem_value name =
  candle_analysis_theorem_trace :=
    name::!candle_analysis_theorem_trace;
  Candle_analysis_theorem name;;

module Candle_analysis_theorem_phrases = struct
  let _ = candle_analysis_theorem_value "REAL_LE_SQUARE_ABS";;
  let _ = candle_analysis_theorem_value "REAL_ABS_REFL";;
  let candle_analysis_theorem_export = true;;
end;;

let candle_analysis_unit_trace = ref ([]:string list);;
let candle_analysis_unit_effect name =
  candle_analysis_unit_trace := name::!candle_analysis_unit_trace;;

module Candle_analysis_unit_phrases = struct
  let _ = candle_analysis_unit_effect "prioritize_num";;
  let _ = candle_analysis_unit_effect "POWER";;
  let _ = candle_analysis_unit_effect "in_dart_of_loop";;
  let _ = candle_analysis_unit_effect "iso";;
  let _ = candle_analysis_unit_effect "translation-short";;
  let _ = candle_analysis_unit_effect "linear-short";;
  let _ = candle_analysis_unit_effect "translation-multiline";;
  let _ = candle_analysis_unit_effect "linear-multiline";;
  let candle_analysis_unit_export = true;;
end;;

let candle_analysis_structure_effect_ok =
  !candle_analysis_theorem_trace =
    ["REAL_ABS_REFL";"REAL_LE_SQUARE_ABS"] &&
  !candle_analysis_unit_trace =
    ["linear-multiline";"translation-multiline";
     "linear-short";"translation-short";
     "iso";"in_dart_of_loop";"POWER";"prioritize_num"] &&
  Candle_analysis_theorem_phrases.candle_analysis_theorem_export &&
  Candle_analysis_unit_phrases.candle_analysis_unit_export;;
