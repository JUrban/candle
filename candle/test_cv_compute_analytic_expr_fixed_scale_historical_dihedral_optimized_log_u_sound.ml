needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound;;

let _ = candle_hist_real_mul_signed_six_sum;;
let _ = candle_fs_hist_delta_gradient_3_real_def;;
let _ = candle_fs_hist_delta_gradient_3_is_expanded;;
let _ = candle_fs_hist_delta_x4_is_gradient_3_expanded;;
let _ = candle_fs_hist_delta_gradient_3_is_delta_x4;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_OPTIMIZED_LOG_U_OK";;
