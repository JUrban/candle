let bool_digit condition = if condition then "1" else "0";;

let float_order_code left right =
  bool_digit (left < right) ^
  bool_digit (left <= right) ^
  bool_digit (left > right) ^
  bool_digit (left >= right);;

let rec float_order_row left = function
  | [] -> ""
  | right :: rest ->
      float_order_code left right ^ float_order_row left rest;;

let rec float_order_matrix values =
  match values with
  | [] -> ""
  | left :: rest ->
      float_order_row left values ^ float_order_matrix rest;;

let float_order_values =
  [nan; neg_infinity; -1.0; -0.0; 0.0; 1.0; infinity];;

print_endline
  ("CANDLE_FLYSPECK_FLOAT_ORDER_MATRIX=" ^
   float_order_matrix float_order_values);;
