(* Focused recovery test for the authentic fourth-sibling group 83.          *)
(* Its one 635-cell component is numerically checked in bounded raw batches, *)
(* then the proved APPEND laws feed the unchanged whole-component topology.   *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunked_function1_state.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_group83_combined_split = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunked_function1_state;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove;;

let rec candle_disjunctive_fourth_group83_nth index = function
  | [] -> failwith "fourth group83 combined split: group underflow"
  | head::tail ->
      if index = 0 then head
      else candle_disjunctive_fourth_group83_nth (index - 1) tail;;

let rec candle_disjunctive_fourth_group83_take count taken remaining =
  if count <= 0 then rev taken,remaining
  else
    match remaining with
    | [] -> rev taken,[]
    | head::tail ->
        candle_disjunctive_fourth_group83_take
          (count - 1) (head::taken) tail;;

let rec candle_disjunctive_fourth_group83_batches limit cells =
  match cells with
  | [] -> []
  | _ ->
      let batch,remaining =
        candle_disjunctive_fourth_group83_take limit [] cells in
      batch :: candle_disjunctive_fourth_group83_batches limit remaining;;

let candle_disjunctive_fourth_group83_components =
  candle_disjunctive_fourth_group83_nth 83
    (candle_disjunctive_fourth_chunk_function1_groups_get ());;

let candle_disjunctive_fourth_group83_cells,
    candle_disjunctive_fourth_group83_tokens,
    candle_disjunctive_fourth_group83_expected_stack =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_fourth_group83_components;;

let candle_disjunctive_fourth_group83_cell_batches =
  candle_disjunctive_fourth_group83_batches 128
    candle_disjunctive_fourth_group83_cells;;

let candle_disjunctive_fourth_group83_raw_results =
  let rec prove index = function
    | [] -> []
    | cells::remaining ->
        print_endline
          ("CANDLE_CV_FOURTH_GROUP83_BOUNDED_RAW_BEGIN" ^
           " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index ^
           " cells=" ^ string_of_int (length cells));
        let result =
          candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
            candle_disjunctive_next_batch_prepared1 cells in
        print_endline
          ("CANDLE_CV_FOURTH_GROUP83_BOUNDED_RAW_END" ^
           " DEVELOPMENT_NON_RELEASE index=" ^ string_of_int index ^
           " cells=" ^ string_of_int (length cells));
        result :: prove (index + 1) remaining in
  prove 0 candle_disjunctive_fourth_group83_cell_batches;;

let candle_disjunctive_fourth_group83_acceptance =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_combine
    candle_disjunctive_fourth_group83_raw_results;;

let candle_disjunctive_fourth_group83_axioms_before = axioms ();;

let candle_disjunctive_fourth_group83_forest =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_combined_split_forest_six
    candle_disjunctive_fourth_group83_acceptance
    (candle_disjunctive_fourth_chunked_f1_logical_tokens
      candle_disjunctive_fourth_group83_tokens)
    (candle_disjunctive_fourth_chunked_f1_encoded_tokens
      candle_disjunctive_fourth_group83_tokens)
    candle_disjunctive_fourth_group83_expected_stack;;

let candle_disjunctive_fourth_group83_axioms_after = axioms ();;

if length candle_disjunctive_fourth_group83_components <> 1 ||
   length candle_disjunctive_fourth_group83_cells <> 635 ||
   length candle_disjunctive_fourth_group83_cell_batches <> 5 ||
   candle_disjunctive_fourth_group83_acceptance.
     fixed_nonlinear_raw_acceptance_compute_count <> 5 ||
   length
     candle_disjunctive_fourth_group83_forest.
       fixed_nonlinear_split_forest_source_theorems <> 1 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       candle_disjunctive_fourth_group83_forest.
         fixed_nonlinear_split_forest_source_theorems) ||
   length candle_disjunctive_fourth_group83_axioms_after <>
     length candle_disjunctive_fourth_group83_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_group83_axioms_before)
       candle_disjunctive_fourth_group83_axioms_after) then
  failwith "fourth group83 combined split: validation failed";;

print_endline
  "CANDLE_CV_FOURTH_GROUP83_COMBINED_SPLIT_OK DEVELOPMENT_NON_RELEASE cells=635 raw_batches=5 roots=1 assumptions=0 frees=0 axiom_growth=0";;

end;;
