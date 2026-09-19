let candle_nonlinear_verifier_array = Array.of_list [3;1;4;1;5];;
let candle_nonlinear_verifier_array_list =
  Array.to_list candle_nonlinear_verifier_array;;
let candle_nonlinear_verifier_abs = Stdlib.abs_float (0.0 -. 3.5);;
let candle_nonlinear_verifier_ignored = Stdlib.ignore 17;;
let candle_nonlinear_verifier_formatter = Format.std_formatter;;
let candle_nonlinear_verifier_empty_print =
  Format.pp_print_string candle_nonlinear_verifier_formatter "";;

let candle_nonlinear_verifier_runtime_compat_ok =
  candle_nonlinear_verifier_array_list = [3;1;4;1;5] &&
  candle_nonlinear_verifier_abs = 3.5 &&
  candle_nonlinear_verifier_ignored = () &&
  candle_nonlinear_verifier_empty_print = ();;

if candle_nonlinear_verifier_runtime_compat_ok then
  print_string "CANDLE_NONLINEAR_VERIFIER_RUNTIME_COMPAT_OK\n"
else
  failwith "nonlinear verifier runtime compatibility mismatch";;
