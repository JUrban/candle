module Candle_ajripqn_pack1 = struct
  let kiumvtc nonnegative_radius packing =
    nonnegative_radius && packing;;
end;;

module Candle_ajripqn_pack2 = struct
  let kiumvtc packing = packing;;
end;;

module Candle_ajripqn_reexport = struct
  open Candle_ajripqn_pack2;;
end;;

module Candle_ajripqn_original = struct
  open Candle_ajripqn_pack1;;
  open Candle_ajripqn_reexport;;
  let selected = kiumvtc true true;;
end;;

let candle_ajripqn_native_resolution_ok =
  Candle_ajripqn_original.selected = true;;
