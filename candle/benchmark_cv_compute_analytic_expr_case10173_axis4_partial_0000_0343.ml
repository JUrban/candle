(* DEVELOPMENT / NON-RELEASE axis-4 scan of a frozen parent prefix. *)
(* Parent records captured: 344; rejected roots selected: 63. *)
let candle_fixed_outer_parent_scan_label = "case10173-axis4-partial-0000-343";;
let candle_fixed_outer_parent_scan_indices =
  [17;32;35;46;54;84;88;90;101;107;108;112;116;122;133;134;136;146;147;155;156;160;173;174;181;182;183;184;186;190;194;195;196;197;200;201;205;214;215;216;217;218;226;234;246;257;259;266;270;283;284;297;299;301;302;303;304;318;329;331;339;340;341];;
let candle_fixed_outer_parent_scan_include_children = true;;
let candle_fixed_outer_parent_scan_child_axes = [4];;
let candle_fixed_outer_parent_scan_batch_size = 8;;
needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan_batched.ml";;

