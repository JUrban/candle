needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound;;

let _ = candle_fs_hist_result_gradient_real_is_analytic;;
let _ = candle_fs_hist_reference_dihedral_hessian_is_atan;;
let _ = candle_fs_hist_final_hessian_entry_real_is_reference;;
let _ = candle_hist_real_atan_negative_quotient_hessian_symmetric;;
let _ = candle_fs_hist_b_real_jet_hessian_symmetric;;
let _ = candle_fs_hist_reference_dihedral_hessian_symmetric;;
let _ = candle_fs_hist_final_hessian_symmetric_real_is_reference;;
let _ = candle_fs_hist_final_hessian_reference_list_of_seq;;
let _ = candle_fs_hist_final_hessian_reference_contains;;

print_endline "CANDLE_CV_HISTORICAL_DIHEDRAL_OPTIMIZED_HESSIAN_ANALYTIC_OK";;
