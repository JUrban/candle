(* DEVELOPMENT / NON-RELEASE varied genuine axis-4 scan sample. *)
let candle_fixed_outer_parent_scan_label = "case10173-axis4-sample8";;
let candle_fixed_outer_parent_scan_indices =
  [17;831;834;1655;1656;2482;2483;2486];;
let candle_fixed_outer_parent_scan_include_children = true;;
let candle_fixed_outer_parent_scan_child_axes = [4];;
let candle_fixed_outer_parent_scan_batch_size = 8;;
needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan_batched.ml";;
