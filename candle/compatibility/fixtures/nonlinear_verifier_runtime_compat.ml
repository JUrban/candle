let candle_nonlinear_verifier_array = Array.of_list [3;1;4;1;5];;
let candle_nonlinear_verifier_array_list =
  Array.to_list candle_nonlinear_verifier_array;;
let candle_nonlinear_verifier_qualified_abs =
  Stdlib.abs_float (0.0 -. 3.5);;
let candle_nonlinear_verifier_unqualified_abs =
  abs_float (0.0 -. 3.5);;
let candle_nonlinear_verifier_ignored = Stdlib.ignore 17;;
let candle_nonlinear_verifier_formatter = Format.std_formatter;;
let candle_nonlinear_verifier_empty_print =
  Format.pp_print_string candle_nonlinear_verifier_formatter "";;

module Candle_nonlinear_informal_verifier = struct
  type verification_funs = {
    taylor:int; f:int; df:int -> int; ddf:int -> int -> int
  };;
end;;

module Candle_nonlinear_informal_record = struct
  open Candle_nonlinear_informal_verifier;;
  let make taylor f = {
    taylor=taylor; f=f;
    df=(fun _ -> failwith "dummy df");
    ddf=(fun _ _ -> failwith "dummy ddf")
  };;
  let taylor value = value.taylor;;
  let f value = value.f;;
end;;

let candle_nonlinear_verifier_record =
  Candle_nonlinear_informal_record.make 11 13;;
let candle_nonlinear_verifier_projections =
  Candle_nonlinear_informal_record.taylor candle_nonlinear_verifier_record,
  Candle_nonlinear_informal_record.f candle_nonlinear_verifier_record;;

let candle_nonlinear_verifier_runtime_compat_ok =
  candle_nonlinear_verifier_array_list = [3;1;4;1;5] &&
  candle_nonlinear_verifier_qualified_abs = 3.5 &&
  candle_nonlinear_verifier_unqualified_abs = 3.5 &&
  candle_nonlinear_verifier_ignored = () &&
  candle_nonlinear_verifier_empty_print = () &&
  candle_nonlinear_verifier_projections = (11,13);;

if candle_nonlinear_verifier_runtime_compat_ok then
  print_string "CANDLE_NONLINEAR_VERIFIER_RUNTIME_COMPAT_OK\n"
else
  failwith "nonlinear verifier runtime compatibility mismatch";;
