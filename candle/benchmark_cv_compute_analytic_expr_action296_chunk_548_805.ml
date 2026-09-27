(* DEVELOPMENT / NON-RELEASE configuration for a bounded action-296 scan. *)
let rec candle_action296_chunk_scan_range start_index stop_index =
  if start_index > stop_index then []
  else
    start_index ::
    candle_action296_chunk_scan_range (start_index + 1) stop_index;;
let candle_action296_chunk_scan_label = "548-805";;
let candle_action296_chunk_scan_indices =
  candle_action296_chunk_scan_range 548 805;;
needs "candle/benchmark_cv_compute_analytic_expr_action296_chunk_scan_algebraic.ml";;
