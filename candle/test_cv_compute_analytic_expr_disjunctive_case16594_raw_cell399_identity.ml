(* Check the intended left-to-right identity of the repaired raw plan. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_raw_cell399_identity = struct

open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let candle_disjunctive_case16594_raw_cell_same left right =
  aconv
    (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      [left])
    (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      [right]);;

let _,candle_disjunctive_case16594_raw_leaf388_domain =
  List.nth candle_disjunctive_case16594_engine_state.family_engine_leaves 388
and _,candle_disjunctive_case16594_raw_leaf398_domain =
  List.nth candle_disjunctive_case16594_engine_state.family_engine_leaves 398;;

let candle_disjunctive_case16594_raw_leaf388_left_domain,
    candle_disjunctive_case16594_raw_leaf388_right_domain =
  M_verifier.split_domain 6 6 1
    candle_disjunctive_case16594_raw_leaf388_domain;;

let candle_disjunctive_case16594_raw_cell388_matches_leaf388_left =
  candle_disjunctive_case16594_raw_cell_same
    (List.nth candle_disjunctive_case16594_variable_raw_plan_cells 388)
    (candle_disjunctive_case16594_variable_raw_cell
      candle_disjunctive_case16594_raw_leaf388_left_domain)
and candle_disjunctive_case16594_raw_cell389_matches_leaf388_right =
  candle_disjunctive_case16594_raw_cell_same
    (List.nth candle_disjunctive_case16594_variable_raw_plan_cells 389)
    (candle_disjunctive_case16594_variable_raw_cell
      candle_disjunctive_case16594_raw_leaf388_right_domain)
and candle_disjunctive_case16594_raw_cell399_matches_leaf398 =
  candle_disjunctive_case16594_raw_cell_same
    (List.nth candle_disjunctive_case16594_variable_raw_plan_cells 399)
    (candle_disjunctive_case16594_variable_raw_cell
      candle_disjunctive_case16594_raw_leaf398_domain);;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_RAW_CELL399_IDENTITY" ^
   " cell388_leaf388_left=" ^
   (if candle_disjunctive_case16594_raw_cell388_matches_leaf388_left then
      "true"
    else "false") ^
   " cell389_leaf388_right=" ^
   (if candle_disjunctive_case16594_raw_cell389_matches_leaf388_right then
      "true"
    else "false") ^
   " cell399_leaf398_whole=" ^
   (if candle_disjunctive_case16594_raw_cell399_matches_leaf398 then
      "true"
    else "false"));;

if not candle_disjunctive_case16594_raw_cell388_matches_leaf388_left ||
   not candle_disjunctive_case16594_raw_cell389_matches_leaf388_right ||
   not candle_disjunctive_case16594_raw_cell399_matches_leaf398 then
  failwith "case16594 raw cell399 identity: left-to-right ordering defect";;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_RAW_CELL399_IDENTITY_OK DEVELOPMENT_NON_RELEASE";;

end;;
