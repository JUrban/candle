(* ========================================================================== *)
(* Export the exact complete historical call and result for the HOL4 gate.   *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_export = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture;;

let candle_case10173_historical_registered_full_export_path =
  "/project/flyspeck-candle-runs/nl-case10173-registered-full-generated-v1.sml";;

let _ =
  let captured = candle_case10173_historical_registered_full_capture () in
  let equations,call,theorem = captured in
  let channel = open_out candle_case10173_historical_registered_full_export_path in
  candle_registered_write_data_theory channel
    "Mechanically exported from the exact complete genuine case-10173 historical checked call."
    "compute_registeredCase10173HistoricalFullData"
    "registered_case10173_historical_full_ceqs"
    "registered_case10173_historical_full_cexp"
    "registered_case10173_historical_full_result"
    equations
    call
    (rand (concl theorem));
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_FULL_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE equations=" ^
     string_of_int
       (length equations) ^
     " path=" ^ candle_case10173_historical_registered_full_export_path);;

end;;
