(* Unified fifth-batch sources from checkpointed bounded proof groups.       *)
(* DEVELOPMENT / NON-RELEASE.                                                *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_bounded_forests = struct

open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state;;

let candle_disjunctive_fifth_bounded_sources0 =
  candle_disjunctive_fifth_chunked_f0_source_theorems ();;

let candle_disjunctive_fifth_bounded_sources1 =
  candle_disjunctive_fifth_chunked_f1_source_theorems ();;

if length candle_disjunctive_fifth_bounded_sources0 <>
     length candle_disjunctive_fifth_batch_components0 ||
   length candle_disjunctive_fifth_bounded_sources1 <>
     length candle_disjunctive_fifth_batch_components1 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       (candle_disjunctive_fifth_bounded_sources0 @
        candle_disjunctive_fifth_bounded_sources1)) then
  failwith "fifth bounded forests: final validation failed";;

print_endline
  ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FORESTS_OK" ^
   " DEVELOPMENT_NON_RELEASE roots=" ^
   string_of_int (length candle_disjunctive_fifth_batch_components) ^
   " function0_roots=" ^
   string_of_int (length candle_disjunctive_fifth_bounded_sources0) ^
   " function1_roots=" ^
   string_of_int (length candle_disjunctive_fifth_bounded_sources1) ^
   " assumptions=0 frees=0");;

end;;
