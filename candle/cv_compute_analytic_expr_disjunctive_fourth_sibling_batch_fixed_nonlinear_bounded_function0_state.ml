(* Checkpointable fourth function-0 proof state.  This is the bounded         *)
(* counterpart of the legacy one-verdict computation: every committed group *)
(* contains at most 128 numerical cells and already includes topology,       *)
(* soundness handoff, and closed source-theorem validation.                  *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_component_bounded_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Candle_cv_analytic_expr_disjunctive_component_bounded_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

type candle_disjunctive_fourth_bounded_f0_progress = {
  fourth_bounded_f0_completed_groups : int;
  fourth_bounded_f0_remaining_groups : int;
  fourth_bounded_f0_completed_cells : int;
  fourth_bounded_f0_completed_roots : int;
  fourth_bounded_f0_numerical_batches : int;
  fourth_bounded_f0_max_group_cells : int;
};;

let candle_disjunctive_fourth_bounded_f0_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_fourth_bounded_f0_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_fourth_bounded_f0_source_passes
    components sources =
  let rec convert components sources =
    match components,sources with
    | [],[] -> []
    | component::remaining_components,source::remaining_sources ->
        candle_disjunctive_component_bounded_source_pass
          candle_disjunctive_next_batch_prepared0.function_term
          source component.next_batch_component_domain ::
        convert remaining_components remaining_sources
    | _ -> failwith
        "fourth bounded function0: source cardinality drift" in
  (* Compact topology is a stack: roots are returned in reverse input order. *)
  convert (rev components) sources;;

let candle_disjunctive_fourth_bounded_f0_prove_group index components =
  let cells,tokens,expected_stack =
    candle_disjunctive_next_batch_forest components in
  let cell_count = length cells and root_count = length components in
  if cell_count <= 0 ||
     cell_count > candle_disjunctive_fourth_chunk_cell_limit then
    failwith "fourth bounded function0: invalid group size";
  candle_q_dim_analytic_jet_profile_event
    ("fourth-sibling-function0-bounded-chunk-" ^
     string_of_int index ^ "-begin");
  let raw =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
      candle_disjunctive_next_batch_prepared0 cells in
  let forest =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_six
      candle_disjunctive_next_batch_prepared0 raw
      (candle_disjunctive_fourth_bounded_f0_logical_tokens tokens)
      (candle_disjunctive_fourth_bounded_f0_encoded_tokens tokens)
      expected_stack in
  let sources =
    candle_disjunctive_fourth_bounded_f0_source_passes
      components forest.fixed_nonlinear_split_forest_source_theorems in
  if length sources <> root_count ||
     not
       (List.for_all
         (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
         sources) then
    failwith "fourth bounded function0: source validation failed";
  candle_q_dim_analytic_jet_profile_event
    ("fourth-sibling-function0-bounded-chunk-" ^
     string_of_int index ^ "-end");
  sources,cell_count,root_count;;

let candle_disjunctive_fourth_bounded_f0_advance,
    candle_disjunctive_fourth_bounded_f0_progress_get,
    candle_disjunctive_fourth_bounded_f0_completed_sources,
    candle_disjunctive_fourth_bounded_f0_source_theorems =
  let remaining =
    ref (candle_disjunctive_fourth_chunk_function0_groups_get ()) in
  let completed_sources = ref ([]:thm list list) in
  let completed_groups = ref 0 in
  let completed_cells = ref 0 in
  let completed_roots = ref 0 in
  let max_group_cells = ref 0 in
  let progress () =
    {fourth_bounded_f0_completed_groups = !completed_groups;
     fourth_bounded_f0_remaining_groups = length !remaining;
     fourth_bounded_f0_completed_cells = !completed_cells;
     fourth_bounded_f0_completed_roots = !completed_roots;
     fourth_bounded_f0_numerical_batches = !completed_groups;
     fourth_bounded_f0_max_group_cells = !max_group_cells} in
  (* Prepending whole groups preserves the reverse-root order of the one-shot
     compact stack while permitting each group to be checkpointed. *)
  let completed () = List.flatten !completed_sources in
  let advance count =
    let rec advance_groups remaining_count =
      if remaining_count <= 0 then ()
      else
        match !remaining with
        | [] -> ()
        | components::remaining_groups ->
            let index = !completed_groups in
            let sources,cells,roots =
              candle_disjunctive_fourth_bounded_f0_prove_group
                index components in
            completed_sources := sources::(!completed_sources);
            remaining := remaining_groups;
            completed_groups := index + 1;
            completed_cells := !completed_cells + cells;
            completed_roots := !completed_roots + roots;
            max_group_cells := max !max_group_cells cells;
            advance_groups (remaining_count - 1) in
    advance_groups count;
    let state = progress () in
    print_endline
      ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FUNCTION0_PROGRESS" ^
       " DEVELOPMENT_NON_RELEASE completed_groups=" ^
       string_of_int state.fourth_bounded_f0_completed_groups ^
       " remaining_groups=" ^
       string_of_int state.fourth_bounded_f0_remaining_groups ^
       " completed_cells=" ^
       string_of_int state.fourth_bounded_f0_completed_cells ^
       " completed_roots=" ^
       string_of_int state.fourth_bounded_f0_completed_roots ^
       " numerical_batches=" ^
       string_of_int state.fourth_bounded_f0_numerical_batches ^
       " max_group_cells=" ^
       string_of_int state.fourth_bounded_f0_max_group_cells) in
  let source_theorems () =
    if (match !remaining with [] -> false | _ -> true) ||
       !completed_cells <> length candle_disjunctive_fourth_batch_cells0 ||
       !completed_roots <>
         length candle_disjunctive_fourth_batch_components0 then
      failwith "fourth bounded function0 state: incomplete";
    completed () in
  advance,progress,completed,source_theorems;;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FUNCTION0_STATE_OK" ^
   " DEVELOPMENT_NON_RELEASE groups=" ^
   string_of_int
     (length (candle_disjunctive_fourth_chunk_function0_groups_get ())) ^
   " cells=" ^ string_of_int (length candle_disjunctive_fourth_batch_cells0) ^
   " roots=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components0) ^
   " cell_limit=" ^
   string_of_int candle_disjunctive_fourth_chunk_cell_limit);;

end;;
