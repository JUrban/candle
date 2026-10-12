(* Focused closed-theorem test for historical certified soundness. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_certified_sound.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_certified_sound;;

let _ = candle_cv_case10173_hist_program_q_result_correct;;
let _ = candle_cv_case10173_hist_finish_q_result_correct;;
let _ = candle_cv_case10173_hist_certified_check_correct;;
let _ = candle_q_dim_taylor_model_invariant_upper_sound;;
let _ = candle_q_dim_taylor_model_invariant_accept_sound;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_CERTIFIED_SOUND_OK";;
