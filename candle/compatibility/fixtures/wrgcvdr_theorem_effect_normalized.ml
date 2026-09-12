module Candle_wrgcvdr_theorem_effect_normalized = struct
  let before = TRUTH;;
  let _ = prove(`T`,REWRITE_TAC[]);;
  let after = TRUTH;;
end;;

let candle_wrgcvdr_theorem_effect_ok =
  concl Candle_wrgcvdr_theorem_effect_normalized.before = `T` &&
  concl Candle_wrgcvdr_theorem_effect_normalized.after = `T`;;
