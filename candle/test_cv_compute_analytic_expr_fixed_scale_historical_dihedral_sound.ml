needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;

let _ = candle_cv_fs_hist_positive_inv_correct;;
let _ = candle_fs_hist_positive_inv_contains;;
let _ = candle_fs_angle_interval_scale_contains;;
let _ = candle_cv_fs_hist_two_over_positive_root_correct;;
let _ = candle_fs_hist_two_over_positive_root_contains;;
let _ = candle_cv_fs_hist_inv_twice_positive_correct;;
let _ = candle_fs_hist_inv_twice_positive_contains;;
let _ = candle_cv_fs_hist_over_twice_positive_correct;;
let _ = candle_fs_hist_over_twice_positive_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_SCALAR_SOUND_OK";;
