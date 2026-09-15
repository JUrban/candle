let candle_array_assignment_values = [|0; 1; 2|];;
let candle_array_assignment_alias = candle_array_assignment_values;;
let candle_array_assignment_result =
  candle_array_assignment_alias.(1) <- 17;;

let candle_array_assignment_nested =
  [|[|10; 11|]; [|20; 21|]|];;
let _ = candle_array_assignment_nested.(1).(0) <- 29;;

let candle_array_assignment_bounds =
  try
    let _ = candle_array_assignment_values.(9) <- 99 in false
  with Invalid_argument _ -> true;;

let candle_ocaml_array_assignment_ok =
  candle_array_assignment_result = () &&
  candle_array_assignment_values = [|0; 17; 2|] &&
  candle_array_assignment_nested = [|[|10; 11|]; [|29; 21|]|] &&
  candle_array_assignment_bounds;;

let _ =
  if candle_ocaml_array_assignment_ok then
    print_endline "CANDLE_OCAML_ARRAY_ASSIGNMENT_OK"
  else
    failwith "OCaml array-assignment compatibility mismatch";;
