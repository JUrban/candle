(* Checkpointable bounded proof state for both fifth-sibling numerical        *)
(* functions.  A group is committed only after raw computation, topology,   *)
(* soundness handoff, and closed source-theorem validation have all passed.  *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunk_plan.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_component_bounded_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunked_state = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Candle_cv_analytic_expr_disjunctive_component_bounded_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

type candle_disjunctive_fifth_chunked_progress = {
  fifth_chunked_completed_groups : int;
  fifth_chunked_remaining_groups : int;
  fifth_chunked_completed_cells : int;
  fifth_chunked_completed_roots : int;
  fifth_chunked_numerical_batches : int;
  fifth_chunked_reflected_subtrees : int;
  fifth_chunked_max_subtree_cells : int;
};;

let candle_disjunctive_fifth_chunked_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_fifth_chunked_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_fifth_chunked_source_passes
    prepared components sources =
  let rec convert components sources =
    match components,sources with
    | [],[] -> []
    | component::remaining_components,source::remaining_sources ->
        candle_disjunctive_component_bounded_source_pass
          prepared.function_term source component.next_batch_component_domain ::
        convert remaining_components remaining_sources
    | _ -> failwith "fifth sibling chunk: source cardinality drift" in
  convert (rev components) sources;;

let candle_disjunctive_fifth_chunked_prove_group
    lane index prepared components =
  let cells,tokens,expected_stack =
    candle_disjunctive_next_batch_forest components in
  candle_q_dim_analytic_jet_profile_event
    ("fifth-sibling-" ^ lane ^ "-chunk-" ^
     string_of_int index ^ "-begin");
  let cell_count = length cells and root_count = length components in
  let sources,numerical_batches,reflected_subtrees,max_subtree_cells =
    if cell_count <= candle_disjunctive_fifth_chunk_cell_limit then
      let raw =
        candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
          prepared cells in
      let forest =
        candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_six
          prepared raw
          (candle_disjunctive_fifth_chunked_logical_tokens tokens)
          (candle_disjunctive_fifth_chunked_encoded_tokens tokens)
          expected_stack in
      candle_disjunctive_fifth_chunked_source_passes
        prepared components forest.fixed_nonlinear_split_forest_source_theorems,
      1,1,cell_count
    else
      match components with
      | [component] ->
          let result =
            candle_disjunctive_component_bounded_prove
              prepared candle_disjunctive_fifth_chunk_cell_limit component in
          [result.component_bounded_list_theorem],
          result.component_bounded_numerical_batches,
          result.component_bounded_reflected_subtrees,
          result.component_bounded_max_subtree_cells
      | _ -> failwith "fifth sibling chunk: oversized non-singleton group" in
  if length sources <> root_count ||
     max_subtree_cells > candle_disjunctive_fifth_chunk_cell_limit ||
     not
       (List.for_all
         (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
         sources) then
    failwith "fifth sibling chunk: source validation failed";
  candle_q_dim_analytic_jet_profile_event
    ("fifth-sibling-" ^ lane ^ "-chunk-" ^
     string_of_int index ^ "-end");
  sources,cell_count,root_count,numerical_batches,
  reflected_subtrees,max_subtree_cells;;

let candle_disjunctive_fifth_chunked_make_state
    lane prepared initial_groups expected_cells expected_roots =
  let remaining = ref initial_groups in
  let completed_sources = ref ([]:thm list list) in
  let completed_groups = ref 0 in
  let completed_cells = ref 0 in
  let completed_roots = ref 0 in
  let numerical_batches = ref 0 in
  let reflected_subtrees = ref 0 in
  let max_subtree_cells = ref 0 in
  let progress () =
    {fifth_chunked_completed_groups = !completed_groups;
     fifth_chunked_remaining_groups = length !remaining;
     fifth_chunked_completed_cells = !completed_cells;
     fifth_chunked_completed_roots = !completed_roots;
     fifth_chunked_numerical_batches = !numerical_batches;
     fifth_chunked_reflected_subtrees = !reflected_subtrees;
     fifth_chunked_max_subtree_cells = !max_subtree_cells} in
  let advance count =
    let rec advance_groups remaining_count =
      if remaining_count <= 0 then ()
      else
        match !remaining with
        | [] -> ()
        | components::remaining_groups ->
            let index = !completed_groups in
            let sources,cells,roots,batches,subtrees,max_cells =
              candle_disjunctive_fifth_chunked_prove_group
                lane index prepared components in
            completed_sources := sources::(!completed_sources);
            remaining := remaining_groups;
            completed_groups := index + 1;
            completed_cells := !completed_cells + cells;
            completed_roots := !completed_roots + roots;
            numerical_batches := !numerical_batches + batches;
            reflected_subtrees := !reflected_subtrees + subtrees;
            max_subtree_cells := max !max_subtree_cells max_cells;
            advance_groups (remaining_count - 1) in
    advance_groups count;
    let state = progress () in
    print_endline
      ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_CHUNKED_PROGRESS" ^
       " DEVELOPMENT_NON_RELEASE lane=" ^ lane ^
       " completed_groups=" ^
       string_of_int state.fifth_chunked_completed_groups ^
       " remaining_groups=" ^
       string_of_int state.fifth_chunked_remaining_groups ^
       " completed_cells=" ^
       string_of_int state.fifth_chunked_completed_cells ^
       " completed_roots=" ^
       string_of_int state.fifth_chunked_completed_roots ^
       " numerical_batches=" ^
       string_of_int state.fifth_chunked_numerical_batches ^
       " reflected_subtrees=" ^
       string_of_int state.fifth_chunked_reflected_subtrees ^
       " max_subtree_cells=" ^
       string_of_int state.fifth_chunked_max_subtree_cells) in
  let source_theorems () =
    if (match !remaining with [] -> false | _ -> true) ||
       !completed_cells <> expected_cells ||
       !completed_roots <> expected_roots then
      failwith ("fifth sibling chunked state incomplete: " ^ lane);
    List.flatten !completed_sources in
  advance,progress,source_theorems;;

let candle_disjunctive_fifth_chunked_f0_advance,
    candle_disjunctive_fifth_chunked_f0_progress_get,
    candle_disjunctive_fifth_chunked_f0_source_theorems =
  candle_disjunctive_fifth_chunked_make_state
    "function0" candle_disjunctive_next_batch_prepared0
    (candle_disjunctive_fifth_chunk_function0_groups_get ())
    (length candle_disjunctive_fifth_batch_cells0)
    (length candle_disjunctive_fifth_batch_components0);;

let candle_disjunctive_fifth_chunked_f1_advance,
    candle_disjunctive_fifth_chunked_f1_progress_get,
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
