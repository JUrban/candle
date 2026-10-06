(* Checkpointable bounded proof state for both fifth-sibling numerical        *)
(* functions.  A group is committed only after raw computation, topology,   *)
(* soundness handoff, and closed source-theorem validation have all passed.  *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunk_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fifth_chunked_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_fifth_chunked_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_fifth_chunked_prove_group
    lane index prepared components =
  let cells,tokens,expected_stack =
    candle_disjunctive_next_batch_forest components in
  candle_q_dim_analytic_jet_profile_event
    ("fifth-sibling-" ^ lane ^ "-chunk-" ^
     string_of_int index ^ "-begin");
  let raw =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
      prepared cells in
  let forest =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_six
      prepared raw
      (candle_disjunctive_fifth_chunked_logical_tokens tokens)
      (candle_disjunctive_fifth_chunked_encoded_tokens tokens)
      expected_stack in
  let sources = forest.fixed_nonlinear_split_forest_source_theorems in
  if length sources <> length components ||
     not
       (List.for_all
         (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
         sources) then
    failwith "fifth sibling chunk: source validation failed";
  candle_q_dim_analytic_jet_profile_event
    ("fifth-sibling-" ^ lane ^ "-chunk-" ^
     string_of_int index ^ "-end");
  sources,length cells,length components;;

let candle_disjunctive_fifth_chunked_make_state
    lane prepared initial_groups expected_cells expected_roots =
  let remaining = ref initial_groups in
  let completed_sources = ref ([]:thm list list) in
  let completed_groups = ref 0 in
  let completed_cells = ref 0 in
  let completed_roots = ref 0 in
  let advance count =
    let rec advance_groups remaining_count =
      if remaining_count <= 0 then ()
      else
        match !remaining with
        | [] -> ()
        | components::remaining_groups ->
            let index = !completed_groups in
            let sources,cells,roots =
              candle_disjunctive_fifth_chunked_prove_group
                lane index prepared components in
            completed_sources := sources::(!completed_sources);
            remaining := remaining_groups;
            completed_groups := index + 1;
            completed_cells := !completed_cells + cells;
            completed_roots := !completed_roots + roots;
            advance_groups (remaining_count - 1) in
    advance_groups count;
    print_endline
      ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_CHUNKED_PROGRESS" ^
       " DEVELOPMENT_NON_RELEASE lane=" ^ lane ^
       " completed_groups=" ^ string_of_int !completed_groups ^
       " remaining_groups=" ^ string_of_int (length !remaining) ^
       " completed_cells=" ^ string_of_int !completed_cells ^
       " completed_roots=" ^ string_of_int !completed_roots) in
  let source_theorems () =
    if (match !remaining with [] -> false | _ -> true) ||
       !completed_cells <> expected_cells ||
       !completed_roots <> expected_roots then
      failwith ("fifth sibling chunked state incomplete: " ^ lane);
    List.flatten !completed_sources in
  advance,source_theorems;;

let candle_disjunctive_fifth_chunked_f0_advance,
    candle_disjunctive_fifth_chunked_f0_source_theorems =
  candle_disjunctive_fifth_chunked_make_state
    "function0" candle_disjunctive_next_batch_prepared0
    (candle_disjunctive_fifth_chunk_function0_groups_get ())
    (length candle_disjunctive_fifth_batch_cells0)
    (length candle_disjunctive_fifth_batch_components0);;

let candle_disjunctive_fifth_chunked_f1_advance,
    candle_disjunctive_fifth_chunked_f1_source_theorems =
  candle_disjunctive_fifth_chunked_make_state
    "function1" candle_disjunctive_next_batch_prepared1
    (candle_disjunctive_fifth_chunk_function1_groups_get ())
    (length candle_disjunctive_fifth_batch_cells1)
    (length candle_disjunctive_fifth_batch_components1);;

print_endline
  ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_CHUNKED_STATE_OK" ^
   " DEVELOPMENT_NON_RELEASE function0_groups=" ^
   string_of_int
     (length (candle_disjunctive_fifth_chunk_function0_groups_get ())) ^
   " function1_groups=" ^
   string_of_int
     (length (candle_disjunctive_fifth_chunk_function1_groups_get ())));;

end;;
