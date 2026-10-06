(* Advance the checkpointed bounded fourth function-1 proof by ten groups. *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state.ml";;

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state;;

let _ = candle_disjunctive_fourth_bounded_f1_advance 10;;

print_endline
  "CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FUNCTION1_ADVANCE_OK DEVELOPMENT_NON_RELEASE";;
