(* Exact first-32-cell fixture shared by matched checker-state discriminators. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_disjunctive_case16594_prefix32_state_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 prefix32 state fixture: short plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_prefix32_state_take (count - 1) tail;;

let candle_disjunctive_case16594_prefix32_state_prepare () =
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_prefix32_state_take 32
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let encoded =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  prepared,encoded;;

let candle_disjunctive_case16594_prefix32_state_term_digest term =
  Digest.to_hex (Digest.string (string_of_term term));;

end;;
