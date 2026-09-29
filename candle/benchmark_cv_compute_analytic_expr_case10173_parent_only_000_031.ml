(* DEVELOPMENT / NON-RELEASE parent-only first-pass configuration. *)
let rec candle_case10173_parent_only_range start_index stop_index =
  if start_index > stop_index then []
  else
    start_index ::
    candle_case10173_parent_only_range (start_index + 1) stop_index;;
let candle_fixed_outer_parent_scan_label = "case10173-parent-only-000-031";;
let candle_fixed_outer_parent_scan_indices =
  candle_case10173_parent_only_range 0 31;;
let candle_fixed_outer_parent_scan_include_children = false;;
needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan.ml";;
