(* Advance the checkpointed fifth-sibling function-0 proof by ten groups. *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state.ml";;

open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state;;

let _ = candle_disjunctive_fifth_chunked_f0_advance 10;;

print_endline
  "CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_CHUNKED_FUNCTION0_ADVANCE_OK DEVELOPMENT_NON_RELEASE";;
