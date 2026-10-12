(* Focused closed-theorem test for the case-10173 historical program splice. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_sound.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_program_sound;;

let _ = candle_cv_case10173_hist_splice_final_eight;;
let _ = candle_cv_case10173_hist_program_run_final;;
let _ = candle_cv_case10173_hist_program_correct;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_PROGRAM_SOUND_OK";;
