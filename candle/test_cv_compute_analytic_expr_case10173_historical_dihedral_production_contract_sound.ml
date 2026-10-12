(* Focused closed-theorem test for the checked historical production bridge. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_production_contract_sound.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_production_contract_sound;;

let _ = candle_fs_hist_positive_interval_components;;
let _ = candle_fs_hist_positive_root_certificate_input_interval;;
let _ = candle_fs_hist_positive_root_certificate_root_interval;;
let _ = candle_fs_hist_positive_interval_contains_positive;;
let _ = candle_fs_hist_scale_four_root_input_positive;;
let _ = candle_case10173_hist_source_dihedral_regular;;
let _ = candle_case10173_hist_first_order_direct_gradient_length;;
let _ = candle_case10173_hist_first_order_reference_contains;;
let _ = candle_case10173_hist_second_order_reference_hessian_contains;;
let _ = candle_case10173_hist_result_jet_shape;;
let _ = candle_case10173_hist_reference_hessian_is_source;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_PRODUCTION_CONTRACT_SOUND_OK";;
