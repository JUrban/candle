needs "candle/cv_compute_analytic_expr_fixed_scale_historical_root_four_x0_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;

let _ = candle_fs_hist_four_x0_gradient_contains;;
let _ = candle_fs_hist_four_x0_hessian_contains;;
let _ = candle_fs_hist_four_x0_hessian_real_symmetric;;
let _ = candle_fs_hist_four_x0_second_value_contains;;
let _ = candle_fs_hist_four_x0_second_data_shape;;
let _ = candle_fs_hist_four_x0_second_to_q_shape;;
let _ = candle_fs_hist_four_x0_second_components;;
let _ = candle_fs_hist_root_four_x0_components;;

print_endline "CANDLE_CV_HISTORICAL_ROOT_FOUR_X0_SOUND_OK";;
