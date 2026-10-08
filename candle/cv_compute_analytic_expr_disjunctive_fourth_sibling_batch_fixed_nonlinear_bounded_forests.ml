(* Unified checkpointed fourth-batch forest sources.  Both numerical        *)
(* functions are proved in bounded batches; no theorem handoff traverses the *)
(* former monolithic 1,921-root conjunction.  DEVELOPMENT / NON-RELEASE.    *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_forests = struct

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state;;

let candle_disjunctive_fourth_bounded_sources0 =
  candle_disjunctive_fourth_bounded_f0_source_theorems ();;

let candle_disjunctive_fourth_bounded_sources1 =
  candle_disjunctive_fourth_bounded_f1_source_theorems ();;

if length candle_disjunctive_fourth_bounded_sources0 <>
     length candle_disjunctive_fourth_batch_components0 ||
   length candle_disjunctive_fourth_bounded_sources1 <>
     length candle_disjunctive_fourth_batch_components1 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       (candle_disjunctive_fourth_bounded_sources0 @
        candle_disjunctive_fourth_bounded_sources1)) then
  failwith "fourth bounded forests: final validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FORESTS_OK" ^
   " DEVELOPMENT_NON_RELEASE roots=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components) ^
   " function0_roots=" ^
   string_of_int (length candle_disjunctive_fourth_bounded_sources0) ^
   " function1_roots=" ^
   string_of_int (length candle_disjunctive_fourth_bounded_sources1) ^
   " function0_numerical_batches=" ^
   string_of_int
     (candle_disjunctive_fourth_bounded_f0_progress_get ()).
       fourth_bounded_f0_numerical_batches ^
   " assumptions=0 frees=0");;

end;;
