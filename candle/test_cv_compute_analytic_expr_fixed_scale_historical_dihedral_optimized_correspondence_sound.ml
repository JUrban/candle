needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;

let _ = candle_fs_hist_b_value_contains;;
let _ = candle_fs_hist_root_delta_gradient_fixed_contains;;
let _ = candle_fs_hist_root_four_x0_gradient_fixed_contains;;
let _ = candle_fs_hist_b_gradient_target_eq;;
let _ = candle_fs_hist_b_gradient_contains;;
let _ = candle_fs_hist_b_gradient_fixed_contains;;
let _ = candle_fs_hist_root_delta_hessian_fixed_contains;;
let _ = candle_fs_hist_matrix_scale_eq;;
let _ = candle_fs_hist_b_base_hessian_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_OPTIMIZED_CORRESPONDENCE_OK";;
