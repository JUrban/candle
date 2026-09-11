type candle_nonlinear_structure_datum = {
  candle_nonlinear_structure_id : string;
  candle_nonlinear_structure_enabled : bool
};;

let candle_nonlinear_structure_trace = ref ([]:string list);;
let candle_nonlinear_structure_emit name =
  candle_nonlinear_structure_trace :=
    name::!candle_nonlinear_structure_trace;;

module Candle_nonlinear_structure_effects = struct
  candle_nonlinear_structure_emit "first";
  candle_nonlinear_structure_emit "second";;
  {
    candle_nonlinear_structure_id = "discarded";
    candle_nonlinear_structure_enabled = false
  };;
end;;
