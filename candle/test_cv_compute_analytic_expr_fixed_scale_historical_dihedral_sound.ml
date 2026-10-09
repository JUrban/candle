needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;

let _ = candle_cv_fs_hist_positive_inv_correct;;
let _ = candle_fs_hist_positive_inv_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_SCALAR_SOUND_OK";;
