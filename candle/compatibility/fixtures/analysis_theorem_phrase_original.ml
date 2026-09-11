type candle_analysis_theorem = Candle_analysis_theorem of string;;

let candle_analysis_theorem_trace = ref ([]:string list);;
let candle_analysis_theorem_value name =
  candle_analysis_theorem_trace :=
    name::!candle_analysis_theorem_trace;
  Candle_analysis_theorem name;;

module Candle_analysis_theorem_phrases = struct
  candle_analysis_theorem_value "REAL_LE_SQUARE_ABS";;
  candle_analysis_theorem_value "REAL_ABS_REFL";;
  let candle_analysis_theorem_export = true;;
end;;
