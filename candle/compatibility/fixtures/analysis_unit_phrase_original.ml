let candle_analysis_unit_trace = ref ([]:string list);;
let candle_analysis_unit_effect name =
  candle_analysis_unit_trace := name::!candle_analysis_unit_trace;;

module Candle_analysis_unit_phrases = struct
  candle_analysis_unit_effect "prioritize_num";;
  candle_analysis_unit_effect "POWER";;
  candle_analysis_unit_effect "in_dart_of_loop";;
  candle_analysis_unit_effect "iso";;
  let candle_analysis_unit_export = true;;
end;;
