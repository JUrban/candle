(* Thirty-two genuine numerical cells spread across the complete 875-cell
   case-16594 plan.  This fixture tests the lean compute boundary beyond the
   convenient prefix while retaining exact plan data.  DEVELOPMENT /
   NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_state_fixture = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let candle_disjunctive_case16594_stratified32_indices =
  [0;28;56;85;113;141;169;197;226;254;282;310;338;367;395;423;
   451;479;507;536;564;592;620;648;677;705;733;761;789;818;846;874];;

let candle_disjunctive_case16594_stratified32_state_prepare () =
  let all_cells =
    candle_disjunctive_case16594_variable_raw_plan_cells in
  if length all_cells <> 875 ||
     length candle_disjunctive_case16594_stratified32_indices <> 32 then
    failwith "case16594 stratified32 fixture: plan shape drift";
  let cells =
    map (fun index -> List.nth all_cells index)
      candle_disjunctive_case16594_stratified32_indices in
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let encoded =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  prepared,encoded;;

end;;
