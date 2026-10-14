(* ========================================================================== *)
(* Export a non-prefix genuine 16-cell registration discriminator.           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk_export.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk16_at2048_export = struct

open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk_export;;

let candle_case10173_historical_registered_chunk16_at2048_export_path =
  "/project/flyspeck-candle-runs/nl-case10173-registered-chunk16-at2048-generated-v1.sml";;

let _ =
  candle_case10173_historical_registered_export_chunk
    2048 16
    candle_case10173_historical_registered_chunk16_at2048_export_path;;

end;;
