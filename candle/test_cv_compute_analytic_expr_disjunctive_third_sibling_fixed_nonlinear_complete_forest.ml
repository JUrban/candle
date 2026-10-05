(* Real third-batch complete fixed-nonlinear forest integration.             *)
(* DEVELOPMENT / NON-RELEASE.                                                *)

needs "candle/cv_compute_analytic_expr_disjunctive_third_sibling_batch_complete_forests.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_third_sibling_fixed_nonlinear_complete_forest = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_third_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_third_sibling_batch_complete_compute;;
open Candle_cv_analytic_expr_disjunctive_third_sibling_batch_complete_forests;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let rec candle_disjunctive_third_batch_fixed_nonlinear_same_theorems
    fixed_outer fixed_nonlinear =
  match fixed_outer,fixed_nonlinear with
  | [],[] -> true
  | outer_head::outer_tail,nonlinear_head::nonlinear_tail ->
      hyp outer_head = [] && hyp nonlinear_head = [] &&
      frees (concl outer_head) = [] && frees (concl nonlinear_head) = [] &&
      aconv (concl outer_head) (concl nonlinear_head) &&
      candle_disjunctive_third_batch_fixed_nonlinear_same_theorems
        outer_tail nonlinear_tail
  | _ -> false;;

let _ =
  let axioms_before = axioms () in
  let complete_call prepared encoded_tokens encoded_jobs =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;encoded_tokens;
        encoded_jobs]) in
  let call0 =
    complete_call candle_disjunctive_next_batch_prepared0
      candle_disjunctive_third_batch_encoded_tokens0
      candle_disjunctive_third_batch_encoded_jobs0
  and call1 =
    complete_call candle_disjunctive_next_batch_prepared1
      candle_disjunctive_third_batch_encoded_tokens1
      candle_disjunctive_third_batch_encoded_jobs1 in
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_FUNCTION0_BEGIN DEVELOPMENT_NON_RELEASE";
  let compute0 =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
      call0 in
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_FUNCTION0_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_FUNCTION1_BEGIN DEVELOPMENT_NON_RELEASE";
  let compute1 =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
      call1 in
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_FUNCTION1_END DEVELOPMENT_NON_RELEASE";
  if not
       (candle_disjunctive_third_batch_computed_accepts
         "fixed nonlinear third batch function0" call0 compute0) ||
     not
       (candle_disjunctive_third_batch_computed_accepts
         "fixed nonlinear third batch function1" call1 compute1) then
    failwith "fixed nonlinear third complete forest: reflected rejection";
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_HANDOFF_BEGIN DEVELOPMENT_NON_RELEASE";
  let forest0 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
      candle_disjunctive_next_batch_prepared0
      candle_disjunctive_third_batch_logical_tokens0
      candle_disjunctive_third_batch_encoded_tokens0
      candle_disjunctive_third_batch_encoded_jobs0 compute0
      candle_disjunctive_third_batch_expected_stack0
  and forest1 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
      candle_disjunctive_next_batch_prepared1
      candle_disjunctive_third_batch_logical_tokens1
      candle_disjunctive_third_batch_encoded_tokens1
      candle_disjunctive_third_batch_encoded_jobs1 compute1
      candle_disjunctive_third_batch_expected_stack1 in
  print_endline
    "CANDLE_CV_FSN_THIRD_COMPLETE_HANDOFF_END DEVELOPMENT_NON_RELEASE";
  let sources0 =
    forest0.fixed_nonlinear_variable_complete_forest_source_theorems
  and sources1 =
    forest1.fixed_nonlinear_variable_complete_forest_source_theorems in
  let outer0 =
    candle_disjunctive_third_batch_forest0.
      variable_complete_forest_source_theorems
  and outer1 =
    candle_disjunctive_third_batch_forest1.
      variable_complete_forest_source_theorems in
  let axioms_after = axioms () in
  if length sources0 <> length candle_disjunctive_third_batch_components0 ||
     length sources1 <> length candle_disjunctive_third_batch_components1 ||
     not
       (candle_disjunctive_third_batch_fixed_nonlinear_same_theorems
         outer0 sources0) ||
     not
       (candle_disjunctive_third_batch_fixed_nonlinear_same_theorems
         outer1 sources1) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "fixed nonlinear third complete forest: validation failed";
  print_endline
    ("CANDLE_CV_FSN_THIRD_COMPLETE_FOREST_OK DEVELOPMENT_NON_RELEASE" ^
     " numerical_cells=" ^
     string_of_int candle_disjunctive_third_batch_total_cells ^
     " roots=" ^
     string_of_int (length sources0 + length sources1) ^
     " function0_roots=" ^ string_of_int (length sources0) ^
     " function1_roots=" ^ string_of_int (length sources1) ^
     " theorem_conclusions_match_fixed_outer=true" ^
     " assumptions=0 frees=0 axiom_growth=0");;

end;;
