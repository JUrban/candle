let flyspeck_debug_setify_term_x = mk_var ("x",bool_ty);;
let flyspeck_debug_setify_term_x_again = mk_var ("x",bool_ty);;
let flyspeck_debug_setify_term_y = mk_var ("y",bool_ty);;

let flyspeck_debug_setify_duplicate_ok =
  length
    (setify Term.(<)
      [flyspeck_debug_setify_term_x;
       flyspeck_debug_setify_term_x_again]) = 1;;

let flyspeck_debug_setify_distinct_ok =
  length
    (setify Term.(<)
      [flyspeck_debug_setify_term_x;
       flyspeck_debug_setify_term_y]) = 2;;

let flyspeck_debug_setify_oracle_ok =
  flyspeck_debug_setify_duplicate_ok &&
  flyspeck_debug_setify_distinct_ok;;

if flyspeck_debug_setify_oracle_ok then ()
else failwith "Flyspeck Debug term setify oracle mismatch";;
