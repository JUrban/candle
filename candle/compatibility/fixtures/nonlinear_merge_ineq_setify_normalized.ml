#use "hol.ml";;

let candle_merge_ineq_x = mk_var ("candle_merge_ineq_x",bool_ty);;
let candle_merge_ineq_y = mk_var ("candle_merge_ineq_y",bool_ty);;

let candle_merge_ineq_bounds =
  [(candle_merge_ineq_y,(candle_merge_ineq_x,candle_merge_ineq_y));
   (candle_merge_ineq_x,(candle_merge_ineq_y,candle_merge_ineq_x));
   (candle_merge_ineq_y,(candle_merge_ineq_x,candle_merge_ineq_y));
   (candle_merge_ineq_x,(candle_merge_ineq_x,candle_merge_ineq_y))];;

let candle_merge_ineq_bound_le x y =
  Pair.compare Term.compare (Pair.compare Term.compare Term.compare)
    x y <= 0;;

let candle_merge_ineq_setify_result =
  setify candle_merge_ineq_bound_le candle_merge_ineq_bounds;;

let candle_merge_ineq_setify_ok =
  candle_merge_ineq_setify_result =
    [(candle_merge_ineq_x,(candle_merge_ineq_x,candle_merge_ineq_y));
     (candle_merge_ineq_x,(candle_merge_ineq_y,candle_merge_ineq_x));
     (candle_merge_ineq_y,(candle_merge_ineq_x,candle_merge_ineq_y))];;

if candle_merge_ineq_setify_ok then ()
else failwith "Flyspeck merge_ineq setify comparator mismatch";;
