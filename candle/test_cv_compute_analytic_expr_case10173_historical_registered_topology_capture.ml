(* Complete compact-topology regression for registered genuine case-10173. *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_topology_capture = struct

open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture;;

let _ =
  let captured =
    candle_case10173_historical_registered_topology_capture () in
  if hyp captured.registered_topology_compute_theorem <> []
  then failwith "case10173 registered topology capture test: drift";
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_TOPOLOGY_CAPTURE_TEST_OK DEVELOPMENT_NON_RELEASE elapsed_seconds=" ^
     string_of_float captured.registered_topology_elapsed_seconds);;

end;;
