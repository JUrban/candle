let candle_packing_flat_term_setify vss =
  let vs = setify Term.(<) (flat vss) in
  map dest_var vs;;

let candle_ssreflect_context_setify tms =
  let vs = setify Term.(<) (flat (map frees tms)) in
  map dest_var vs;;

let candle_packing_flat_term_setify_x = mk_var("x",bool_ty);;
let candle_packing_flat_term_setify_y = mk_var("y",bool_ty);;

let candle_packing_flat_term_setify_ok =
  candle_packing_flat_term_setify
    [[candle_packing_flat_term_setify_y;
      candle_packing_flat_term_setify_x];
     [candle_packing_flat_term_setify_x]] =
  [("x",bool_ty);("y",bool_ty)];;

let candle_ssreflect_context_setify_ok =
  candle_ssreflect_context_setify
    [mk_conj(candle_packing_flat_term_setify_y,
             candle_packing_flat_term_setify_x);
     candle_packing_flat_term_setify_x] =
  [("x",bool_ty);("y",bool_ty)];;

if candle_packing_flat_term_setify_ok &&
   candle_ssreflect_context_setify_ok then ()
else failwith "Flyspeck packing flat-term setify oracle mismatch";;
