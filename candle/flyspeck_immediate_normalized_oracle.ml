(* Candle acceptance and branch witness for the normalized LP expression. *)
let candle_flyspeck_lp_base_case n =
  if n = 1 then [] else [n];;

let candle_flyspeck_immediate_normalized_oracle_ok =
  candle_flyspeck_lp_base_case 1 = [] &&
  candle_flyspeck_lp_base_case 0 = [0] &&
  candle_flyspeck_lp_base_case 2 = [2];;

if candle_flyspeck_immediate_normalized_oracle_ok then () else
  failwith "normalized Candle LP branch mismatch";;
