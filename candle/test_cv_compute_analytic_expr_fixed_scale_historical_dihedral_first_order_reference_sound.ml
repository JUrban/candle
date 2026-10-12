needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_first_order_reference_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_reference_sound;;

let _ = candle_fs_hist_delta_x4_value_direct_contains;;
let _ = candle_fs_angle_delta_value_contains;;
let _ = candle_fs_angle_delta_gradient_contains;;
let _ = candle_fs_hist_root_delta_gradient_direct_contains;;
let _ = candle_fs_hist_b_gradient_direct_contains;;
let _ = candle_fs_hist_c_vector_direct_contains;;
let _ = candle_fs_hist_first_order_direct_reference_value_contains;;
let _ = candle_fs_hist_first_order_direct_reference_gradient_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_FIRST_ORDER_REFERENCE_OK";;
