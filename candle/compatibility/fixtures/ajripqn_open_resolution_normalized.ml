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

module Candle_ajripqn_normalized = struct
  open Candle_ajripqn_pack1;;
  open Candle_ajripqn_reexport;;
  let selected = Candle_ajripqn_pack1.kiumvtc true true;;
end;;

let candle_ajripqn_open_resolution_ok =
  Candle_ajripqn_normalized.selected = true;;
