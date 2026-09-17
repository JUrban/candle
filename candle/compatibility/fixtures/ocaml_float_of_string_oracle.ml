let candle_float_of_string_failure thunk =
  try let _ = thunk () in false
  with Failure message -> message = "float_of_string";;

let candle_float_of_string_ok =
  float_of_string "12.5e2" = 1250.0 &&
  float_of_string "0.125" = 0.125 &&
  Float.of_string "6.25" = 6.25 &&
  candle_float_of_string_failure (fun () -> float_of_string "bad") &&
  candle_float_of_string_failure (fun () -> Float.of_string "bad");;

if candle_float_of_string_ok then
  print_string "CANDLE_OCAML_FLOAT_OF_STRING_OK\n"
else
  failwith "float_of_string compatibility mismatch";;
