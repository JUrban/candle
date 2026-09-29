(* DEVELOPMENT / NON-RELEASE bounded-batch parent scan configuration. *)
let rec candle_case10173_parent_range_0827_1653_batched start_index stop_index =
  if start_index > stop_index then []
  else
    start_index ::
    candle_case10173_parent_range_0827_1653_batched
      (start_index + 1) stop_index;;
let candle_fixed_outer_parent_scan_label =
  "case10173-parent-0827-1653-batched";;
let candle_fixed_outer_parent_scan_indices =
  candle_case10173_parent_range_0827_1653_batched 827 1653;;
let candle_fixed_outer_parent_scan_include_children = false;;
let candle_fixed_outer_parent_scan_child_axes = [];;
let candle_fixed_outer_parent_scan_batch_size = 8;;
needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan_batched.ml";;
