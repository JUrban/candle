(* Value-reuse census for the genuine case-16594 reflected numerical plan. *)
(* DEVELOPMENT / NON-RELEASE: this is an untrusted representation diagnostic. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_plan_reuse = struct

open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_case16594_reuse_mem value = function
  | [] -> false
  | head :: tail -> head = value || candle_case16594_reuse_mem value tail;;

let rec candle_case16594_reuse_unique reversed = function
  | [] -> rev reversed
  | head :: tail ->
      candle_case16594_reuse_unique
        (if candle_case16594_reuse_mem head reversed then reversed
         else head :: reversed)
        tail;;

let candle_case16594_reuse_unique_count values =
  length (candle_case16594_reuse_unique [] values);;

let rec candle_case16594_reuse_append_map select = function
  | [] -> []
  | head :: tail ->
      select head @ candle_case16594_reuse_append_map select tail;;

let candle_case16594_reuse_cells =
  candle_disjunctive_case16594_variable_raw_plan_cells;;

let candle_case16594_reuse_box_vectors =
  map (fun cell -> cell.variable_batch_box_intervals)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_center_vectors =
  map
    (fun cell ->
      cell.variable_batch_stable_cell.stable_batch_center_intervals)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_lower_vectors =
  map (fun cell -> cell.variable_batch_stable_cell.stable_batch_lower)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_upper_vectors =
  map (fun cell -> cell.variable_batch_stable_cell.stable_batch_upper)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_box_items =
  candle_case16594_reuse_append_map
    (fun cell -> cell.variable_batch_box_intervals)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_center_items =
  candle_case16594_reuse_append_map
    (fun cell ->
      cell.variable_batch_stable_cell.stable_batch_center_intervals)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_lower_items =
  candle_case16594_reuse_append_map
    (fun cell -> cell.variable_batch_stable_cell.stable_batch_lower)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_upper_items =
  candle_case16594_reuse_append_map
    (fun cell -> cell.variable_batch_stable_cell.stable_batch_upper)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_interval_items =
  candle_case16594_reuse_box_items @ candle_case16594_reuse_center_items;;

let candle_case16594_reuse_interval_pairs =
  candle_case16594_reuse_append_map
    (fun cell ->
      zip cell.variable_batch_box_intervals
        cell.variable_batch_stable_cell.stable_batch_center_intervals)
    candle_case16594_reuse_cells;;

let candle_case16594_reuse_bound_pairs =
  candle_case16594_reuse_append_map
    (fun cell ->
      zip cell.variable_batch_stable_cell.stable_batch_lower
        cell.variable_batch_stable_cell.stable_batch_upper)
    candle_case16594_reuse_cells;;

let _ =
  let cells = length candle_case16594_reuse_cells
  and unique_cells =
    candle_case16594_reuse_unique_count candle_case16594_reuse_cells
  and box_vectors = length candle_case16594_reuse_box_vectors
  and unique_box_vectors =
    candle_case16594_reuse_unique_count candle_case16594_reuse_box_vectors
  and center_vectors = length candle_case16594_reuse_center_vectors
  and unique_center_vectors =
    candle_case16594_reuse_unique_count candle_case16594_reuse_center_vectors
  and lower_vectors = length candle_case16594_reuse_lower_vectors
  and unique_lower_vectors =
    candle_case16594_reuse_unique_count candle_case16594_reuse_lower_vectors
  and upper_vectors = length candle_case16594_reuse_upper_vectors
  and unique_upper_vectors =
    candle_case16594_reuse_unique_count candle_case16594_reuse_upper_vectors
  and box_items = length candle_case16594_reuse_box_items
  and unique_box_items =
    candle_case16594_reuse_unique_count candle_case16594_reuse_box_items
  and center_items = length candle_case16594_reuse_center_items
  and unique_center_items =
    candle_case16594_reuse_unique_count candle_case16594_reuse_center_items
  and lower_items = length candle_case16594_reuse_lower_items
  and unique_lower_items =
    candle_case16594_reuse_unique_count candle_case16594_reuse_lower_items
  and upper_items = length candle_case16594_reuse_upper_items
  and unique_upper_items =
    candle_case16594_reuse_unique_count candle_case16594_reuse_upper_items
  and interval_items = length candle_case16594_reuse_interval_items
  and unique_interval_items =
    candle_case16594_reuse_unique_count candle_case16594_reuse_interval_items
  and interval_pairs = length candle_case16594_reuse_interval_pairs
  and unique_interval_pairs =
    candle_case16594_reuse_unique_count candle_case16594_reuse_interval_pairs
  and bound_pairs = length candle_case16594_reuse_bound_pairs
  and unique_bound_pairs =
    candle_case16594_reuse_unique_count candle_case16594_reuse_bound_pairs in
  print_endline
    ("CANDLE_CV_CASE16594_PLAN_REUSE" ^
     " cells=" ^ string_of_int cells ^
     " unique_cells=" ^ string_of_int unique_cells ^
     " box_vectors=" ^ string_of_int box_vectors ^
     " unique_box_vectors=" ^ string_of_int unique_box_vectors ^
     " center_vectors=" ^ string_of_int center_vectors ^
     " unique_center_vectors=" ^ string_of_int unique_center_vectors ^
     " lower_vectors=" ^ string_of_int lower_vectors ^
     " unique_lower_vectors=" ^ string_of_int unique_lower_vectors ^
     " upper_vectors=" ^ string_of_int upper_vectors ^
     " unique_upper_vectors=" ^ string_of_int unique_upper_vectors ^
     " box_items=" ^ string_of_int box_items ^
     " unique_box_items=" ^ string_of_int unique_box_items ^
     " center_items=" ^ string_of_int center_items ^
     " unique_center_items=" ^ string_of_int unique_center_items ^
     " lower_items=" ^ string_of_int lower_items ^
     " unique_lower_items=" ^ string_of_int unique_lower_items ^
     " upper_items=" ^ string_of_int upper_items ^
     " unique_upper_items=" ^ string_of_int unique_upper_items ^
     " interval_items=" ^ string_of_int interval_items ^
     " unique_interval_items=" ^ string_of_int unique_interval_items ^
     " interval_pairs=" ^ string_of_int interval_pairs ^
     " unique_interval_pairs=" ^ string_of_int unique_interval_pairs ^
     " bound_pairs=" ^ string_of_int bound_pairs ^
     " unique_bound_pairs=" ^ string_of_int unique_bound_pairs);
  print_endline
    "CANDLE_CV_CASE16594_PLAN_REUSE_OK DEVELOPMENT_NON_RELEASE";;

end;;
