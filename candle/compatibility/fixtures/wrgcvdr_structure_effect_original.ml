module Candle_wrgcvdr_structure_original = struct
  let hypermap = TRUTH;;
  parse_as_infix("candle_has_orders",(12,"right"));;
  parse_as_infix("candle_cyclic_on",(13,"right"));;
end;;

let candle_wrgcvdr_structure_original_ok =
  concl Candle_wrgcvdr_structure_original.hypermap = `T`;;
