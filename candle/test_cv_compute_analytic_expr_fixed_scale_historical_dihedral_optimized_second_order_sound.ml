needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound;;

let _ = candle_fs_hist_second_components_from_data;;
let _ = candle_fs_hist_reference_dihedral_value;;
let _ = candle_fs_hist_special_gradient_real_is_low_work;;
let _ = candle_fs_hist_replace_three_contains;;
let _ = candle_fs_hist_scaled_c_contains;;
let _ = candle_fs_hist_final_gradient_low_work_contains;;
let _ = candle_fs_hist_final_gradient_reference_contains;;
let _ = candle_fs_hist_c_vector_length;;
let _ = candle_fs_hist_special_gradient_fixed_contains;;
let _ = candle_fs_hist_reciprocal_u_fixed_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_OPTIMIZED_SECOND_ORDER_OK";;
