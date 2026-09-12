let candle_packing_flat_term_setify vss =
  let vs = setify (flat vss) in
  map dest_var vs;;

let candle_ssreflect_context_setify tms =
  let vs = setify (flat (map frees tms)) in
  map dest_var vs;;
