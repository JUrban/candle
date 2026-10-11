needs "candle/cv_compute_analytic_expr_fixed_scale_historical_delta_root_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;

let _ = candle_fs_hist_delta_hessian_real_symmetric;;
let _ = candle_fs_hist_delta_hessian_component_real_symmetric;;
let _ = candle_fs_hist_delta_hessian_component_real_list_of_seq;;
let _ = candle_fs_hist_delta_hessian_component_real_in_range;;
let _ = candle_fs_hist_delta_second_symmetric_components;;
let _ = candle_fs_hist_second_eta;;
let _ = candle_fs_hist_delta_second_data_shape;;
let _ = candle_fs_hist_root_delta_components;;

print_endline "CANDLE_CV_HISTORICAL_DELTA_ROOT_SOUND_OK";;
