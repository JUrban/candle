(* Closed source theorems for every fifth-batch homogeneous forest root,    *)
(* produced through the general fixed-nonlinear complete-checker theorem.   *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_complete_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_complete_forests = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fifth_batch_forest0_get,
    candle_disjunctive_fifth_batch_forest1_get =
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-fixed-nonlinear-handoff-begin";
  let forest0 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
      candle_disjunctive_next_batch_prepared0
      candle_disjunctive_fifth_batch_logical_tokens0
      candle_disjunctive_fifth_batch_encoded_tokens0
      candle_disjunctive_fifth_batch_encoded_jobs0
      (candle_disjunctive_fifth_batch_compute0_get ())
      candle_disjunctive_fifth_batch_expected_stack0
  and forest1 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
      candle_disjunctive_next_batch_prepared1
      candle_disjunctive_fifth_batch_logical_tokens1
      candle_disjunctive_fifth_batch_encoded_tokens1
      candle_disjunctive_fifth_batch_encoded_jobs1
      (candle_disjunctive_fifth_batch_compute1_get ())
      candle_disjunctive_fifth_batch_expected_stack1 in
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-fixed-nonlinear-handoff-end";
  let sources0 =
    forest0.fixed_nonlinear_variable_complete_forest_source_theorems
  and sources1 =
    forest1.fixed_nonlinear_variable_complete_forest_source_theorems in
  let axioms_after = axioms () in
  if length sources0 <> length candle_disjunctive_fifth_batch_components0 ||
     length sources1 <> length candle_disjunctive_fifth_batch_components1 ||
     not
       (List.for_all
         (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
         (sources0 @ sources1)) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "fifth sibling batch complete forests: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_COMPLETE_FORESTS_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " roots=" ^
     string_of_int (length candle_disjunctive_fifth_batch_components) ^
     " function0_roots=" ^ string_of_int (length sources0) ^
     " function1_roots=" ^ string_of_int (length sources1) ^
     " assumptions=0 frees=0 axiom_growth=0");
  (fun () -> forest0),(fun () -> forest1);;

end;;
