module Float = struct
  let flyspeck_shadow = true
end;;

(* The clean development checkpoint predates [Stdlib.Float].  Its proved IEEE
   field projections suffice to reconstruct the current Candle comparator
   exactly when a focused restore needs to add that nested module. *)
let candle_checkpoint_float_compare left right =
  let left_sign = Cake.Word64.toInt (Cake.Double.sign left) in
  let right_sign = Cake.Word64.toInt (Cake.Double.sign right) in
  let left_exponent = Cake.Word64.toInt (Cake.Double.exponent left) in
  let right_exponent = Cake.Word64.toInt (Cake.Double.exponent right) in
  let left_significand = Cake.Word64.toInt (Cake.Double.significand left) in
  let right_significand = Cake.Word64.toInt (Cake.Double.significand right) in
  let left_nan = left_exponent = 2047 && not (left_significand = 0) in
  let right_nan = right_exponent = 2047 && not (right_significand = 0) in
  let left_zero = left_exponent = 0 && left_significand = 0 in
  let right_zero = right_exponent = 0 && right_significand = 0 in
  if left_nan || right_nan then 0
  else if left_zero && right_zero then 0
  else if left = right then 0
  else if not (left_sign = right_sign) then
    if left_sign = 0 then 1 else -1
  else
    let magnitude =
      if left_exponent < right_exponent then -1
      else if left_exponent > right_exponent then 1
      else if left_significand < right_significand then -1
      else 1 in
    if left_sign = 0 then magnitude else 0 - magnitude;;

let candle_lpproc_float_feasible r =
  Stdlib.Float.compare r 11.9999 = 1;;

let candle_lpproc_float_compare_ok =
  not (candle_lpproc_float_feasible 0.0) &&
  not (candle_lpproc_float_feasible 11.9999) &&
  candle_lpproc_float_feasible 12.0 &&
  candle_lpproc_float_feasible (1.0 /. 0.0) &&
  not (candle_lpproc_float_feasible (0.0 /. 0.0)) &&
  let zero = 0.0 in
  let values =
    [zero; negfloat zero; 11.9999; 12.0;
     negfloat 12.0; 1.0 /. zero; negfloat (1.0 /. zero);
     zero /. zero] in
  List.for_all
    (fun left ->
       List.for_all
         (fun right ->
            candle_checkpoint_float_compare left right =
            Stdlib.Float.compare left right)
         values)
    values;;

if candle_lpproc_float_compare_ok then
  print_string "CANDLE_LPPROC_FLOAT_COMPARE_OK\n"
else
  failwith "explicit float comparator changed feasibility threshold";;
