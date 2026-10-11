needs "candle/cv_compute_analytic_expr_fixed_scale_historical_delta_x4_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;

let _ = candle_fs_hist_delta_x4_hessian_contains;;
let _ = candle_fs_hist_delta_x4_hessian_real_symmetric;;
let _ = candle_fs_hist_delta_x4_hessian_component_real_symmetric;;
let _ = candle_fs_hist_delta_x4_hessian_component_real_list_of_seq;;
let _ = candle_fs_hist_delta_x4_second_gradient_contains;;
let _ = candle_fs_hist_delta_x4_second_hessian_contains;;
let _ = candle_fs_hist_delta_x4_second_data_shape;;
let _ = candle_fs_hist_delta_x4_second_to_q_shape;;
let _ = candle_fs_hist_delta_x4_second_components;;

print_endline "CANDLE_CV_HISTORICAL_DELTA_X4_SOUND_OK";;
