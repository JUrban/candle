needs "candle/cv_compute_analytic_expr_fixed_scale_historical_root_certificate_compute.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute;;

let _ = candle_cv_fs_hist_root_certificate_correct;;
let _ = candle_fs_hist_root_certificate_contains;;
let _ = candle_cv_fs_hist_root_certificate_reject_outer_num;;
let _ = candle_cv_fs_hist_root_certificate_reject_lower_num;;
let _ = candle_cv_fs_hist_root_certificate_reject_upper_num;;

print_endline "CANDLE_CV_HISTORICAL_ROOT_CERTIFICATE_COMPUTE_OK";;
