(* Closed source theorems for every maximal same-function forest root. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_complete_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_next_sibling_batch_complete_forests = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_next_batch_forests_axioms_before = axioms ();;
let candle_disjunctive_next_batch_forest0 =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_forest_six
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_logical_tokens0
    candle_disjunctive_next_batch_encoded_tokens0
    candle_disjunctive_next_batch_encoded_jobs0
    candle_disjunctive_next_batch_compute0
    candle_disjunctive_next_batch_expected_stack0;;
let candle_disjunctive_next_batch_forest1 =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_forest_six
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_logical_tokens1
    candle_disjunctive_next_batch_encoded_tokens1
    candle_disjunctive_next_batch_encoded_jobs1
    candle_disjunctive_next_batch_compute1
    candle_disjunctive_next_batch_expected_stack1;;
let candle_disjunctive_next_batch_forests_axioms_after = axioms ();;

if length candle_disjunctive_next_batch_forest0.
     variable_complete_forest_source_theorems <>
     length candle_disjunctive_next_batch_components0 ||
   length candle_disjunctive_next_batch_forest1.
     variable_complete_forest_source_theorems <>
     length candle_disjunctive_next_batch_components1 ||
   length candle_disjunctive_next_batch_forests_axioms_after <>
     length candle_disjunctive_next_batch_forests_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_next_batch_forests_axioms_before)
       candle_disjunctive_next_batch_forests_axioms_after) then
  failwith "next sibling batch complete forests: validation failed";;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_COMPLETE_FORESTS_OK DEVELOPMENT_NON_RELEASE" ^
   " roots=" ^
   string_of_int (length candle_disjunctive_next_batch_components) ^
   " function0_roots=" ^
   string_of_int (length candle_disjunctive_next_batch_components0) ^
   " function1_roots=" ^
   string_of_int (length candle_disjunctive_next_batch_components1) ^
   " assumptions=0 axiom_growth=0");;

end;;
