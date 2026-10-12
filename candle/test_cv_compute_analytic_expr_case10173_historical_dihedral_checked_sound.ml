(* Focused closed-theorem test for checked historical auxiliary roots. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_sound.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound;;

let _ = candle_cv_fs_hist_positive_root_certificate_correct;;
let _ = candle_cv_fs_hist_root_list_check_four_correct;;
let _ = candle_cv_case10173_hist_root_inputs_correct;;
let _ = candle_cv_case10173_hist_root_record_check_correct;;
let _ = candle_fs_hist_positive_root_certificate_contains;;
let _ = candle_case10173_hist_root_record_valid_components;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_SOUND_OK";;
