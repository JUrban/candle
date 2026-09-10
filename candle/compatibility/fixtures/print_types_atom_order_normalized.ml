let flyspeck_print_types_bool = bool_ty;;
let flyspeck_print_types_fun = mk_fun_ty bool_ty bool_ty;;

let flyspeck_print_types_atom_lt x y =
  Pair.compare String.compare Type.compare x y < 0;;

let flyspeck_print_types_duplicate = ("a",flyspeck_print_types_bool);;
let flyspeck_print_types_distinct = ("a",flyspeck_print_types_fun);;
let flyspeck_print_types_later = ("z",flyspeck_print_types_bool);;

let flyspeck_print_types_setified =
  setify flyspeck_print_types_atom_lt
    [flyspeck_print_types_later;
     flyspeck_print_types_duplicate;
     flyspeck_print_types_distinct;
     flyspeck_print_types_duplicate];;

let flyspeck_print_types_duplicate_distinct_ok =
  length flyspeck_print_types_setified = 3;;

let flyspeck_print_types_order_ok =
  match sort flyspeck_print_types_atom_lt flyspeck_print_types_setified with
  | [first;second;third] ->
      flyspeck_print_types_atom_lt first second &&
      flyspeck_print_types_atom_lt second third
  | _ -> false;;

let flyspeck_print_types_numeric_comparison_ok = 1 < 2;;

let flyspeck_print_types_concat_ok =
  List.concat [[1;2];[];[3]] = [1;2;3];;

let flyspeck_print_types_atom_order_oracle_ok =
  flyspeck_print_types_duplicate_distinct_ok &&
  flyspeck_print_types_order_ok &&
  flyspeck_print_types_numeric_comparison_ok &&
  flyspeck_print_types_concat_ok;;

if flyspeck_print_types_atom_order_oracle_ok then ()
else failwith "Flyspeck Print_types atom-order oracle mismatch";;
