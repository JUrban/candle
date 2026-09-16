let candle_array_assignment_values = Array.of_list [0; 1; 2];;
let candle_array_assignment_alias = candle_array_assignment_values;;
let candle_array_assignment_result =
  candle_array_assignment_alias.(1) <- 17;;

let candle_array_assignment_nested =
  Array.of_list
    [Array.of_list [10; 11]; Array.of_list [20; 21]];;
let _ = candle_array_assignment_nested.(1).(0) <- 29;;

let candle_array_assignment_bounds =
  try
    let _ = candle_array_assignment_values.(9) <- 99 in false
  with Invalid_argument _ -> true;;

let candle_ocaml_array_assignment_ok =
  candle_array_assignment_result = () &&
  Array.length candle_array_assignment_values = 3 &&
  candle_array_assignment_values.(0) = 0 &&
  candle_array_assignment_values.(1) = 17 &&
  candle_array_assignment_values.(2) = 2 &&
  Array.length candle_array_assignment_nested = 2 &&
  Array.get (Array.get candle_array_assignment_nested 0) 0 = 10 &&
  Array.get (Array.get candle_array_assignment_nested 0) 1 = 11 &&
  Array.get (Array.get candle_array_assignment_nested 1) 0 = 29 &&
  Array.get (Array.get candle_array_assignment_nested 1) 1 = 21 &&
  candle_array_assignment_bounds;;

let _ =
  if candle_ocaml_array_assignment_ok then
    print_endline "CANDLE_OCAML_ARRAY_ASSIGNMENT_OK"
  else
    failwith "OCaml array-assignment compatibility mismatch";;
