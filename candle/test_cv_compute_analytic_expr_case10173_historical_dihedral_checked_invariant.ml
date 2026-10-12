(* Focused closed-theorem test for the complete checked per-cell invariant. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_invariant.ml";;

open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_invariant;;

let _ = candle_case10173_hist_checked_source_contract;;
let _ = candle_case10173_hist_checked_logical_item_source_analytic_invariant;;

print_endline "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_INVARIANT_OK";;
