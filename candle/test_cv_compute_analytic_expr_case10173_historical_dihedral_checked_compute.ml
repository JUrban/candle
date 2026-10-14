(* Focused closed-definition test for the checked historical job wrapper. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;

let _ = candle_cv_fs_hist_root_list_check_compute;;
let _ = candle_cv_case10173_hist_checked_jobs_check_compute;;
let _ = candle_cv_case10173_hist_checked_raw_jobs_accept;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_COMPUTE_OK";;
