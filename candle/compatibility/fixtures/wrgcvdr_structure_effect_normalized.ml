module Candle_wrgcvdr_structure_normalized = struct
  let hypermap = TRUTH;;
  let _ = parse_as_infix("candle_has_orders",(12,"right"));;
  let _ = parse_as_infix("candle_cyclic_on",(13,"right"));;
end;;

let candle_wrgcvdr_structure_effect_ok =
  concl Candle_wrgcvdr_structure_normalized.hypermap = `T`;;
