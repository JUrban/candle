module Candle_wrgcvdr_theorem_effect_original = struct
  let before = TRUTH;;
  prove(`T`,REWRITE_TAC[]);;
  let after = TRUTH;;
end;;

let candle_wrgcvdr_theorem_original_ok =
  concl Candle_wrgcvdr_theorem_effect_original.before = `T` &&
  concl Candle_wrgcvdr_theorem_effect_original.after = `T`;;
