type candle_merge_qualified_record = {
  ineq : int
};;

module Candle_merge_qualified_source = struct
  let TSKAJXY_DERIVED = {ineq = 7};;
end;;

let candle_merge_qualified_result =
  Candle_merge_qualified_source.TSKAJXY_DERIVED.ineq;;
