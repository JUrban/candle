(* ========================================================================== *)
(* Four disjoint genuine case-16594 subtrees computed in one lean session.   *)
(*                                                                            *)
(* Every sample is a complete authenticated subtree, not an arbitrary job    *)
(* slice. Intermediate numerical and topology values remain cval data until  *)
(* the late shared soundness layer is loaded.                                 *)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_subtree_batch_precomputed_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

type candle_disjunctive_case16594_complete_subtree_batch_token_data =
  | Candle_disjunctive_case16594_complete_subtree_batch_leaf
  | Candle_disjunctive_case16594_complete_subtree_batch_glue of int;;

let rec candle_disjunctive_case16594_complete_subtree_batch_count = function
  | Candle_disjunctive_case16594_variable_axis_leaf _ -> 1
  | Candle_disjunctive_case16594_variable_axis_node (_,left,right) ->
      candle_disjunctive_case16594_complete_subtree_batch_count left +
      candle_disjunctive_case16594_complete_subtree_batch_count right;;

let rec candle_disjunctive_case16594_complete_subtree_batch_find
    start target_start target_count shape =
  let count =
    candle_disjunctive_case16594_complete_subtree_batch_count shape in
  if start = target_start && count = target_count then shape
  else
    match shape with
    | Candle_disjunctive_case16594_variable_axis_leaf _ ->
        failwith "case16594 complete subtree batch: target is not a subtree"
    | Candle_disjunctive_case16594_variable_axis_node (_,left,right) ->
        let left_count =
          candle_disjunctive_case16594_complete_subtree_batch_count left in
        if target_start < start + left_count then
          candle_disjunctive_case16594_complete_subtree_batch_find
            start target_start target_count left
        else
          candle_disjunctive_case16594_complete_subtree_batch_find
            (start + left_count) target_start target_count right;;

let rec candle_disjunctive_case16594_complete_subtree_batch_cells = function
  | Candle_disjunctive_case16594_variable_axis_leaf cell -> [cell]
  | Candle_disjunctive_case16594_variable_axis_node (_,left,right) ->
      candle_disjunctive_case16594_complete_subtree_batch_cells left @
      candle_disjunctive_case16594_complete_subtree_batch_cells right;;

let rec candle_disjunctive_case16594_complete_subtree_batch_tokens = function
  | Candle_disjunctive_case16594_variable_axis_leaf _ ->
      [Candle_disjunctive_case16594_complete_subtree_batch_leaf]
  | Candle_disjunctive_case16594_variable_axis_node (axis,left,right) ->
      candle_disjunctive_case16594_complete_subtree_batch_tokens left @
      candle_disjunctive_case16594_complete_subtree_batch_tokens right @
      [Candle_disjunctive_case16594_complete_subtree_batch_glue axis];;

let candle_disjunctive_case16594_complete_subtree_batch_encode_token = function
  | Candle_disjunctive_case16594_complete_subtree_batch_leaf -> `Cexp_num 0`
  | Candle_disjunctive_case16594_complete_subtree_batch_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let rec candle_disjunctive_case16594_complete_subtree_batch_stack_length
    encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete subtree batch stack" encoded in
    1 +
    candle_disjunctive_case16594_complete_subtree_batch_stack_length tail;;

type candle_disjunctive_case16594_complete_subtree_batch_segment_capture = {
  complete_subtree_batch_start : int;
  complete_subtree_batch_cells : int;
  complete_subtree_batch_root_axis : int;
  complete_subtree_batch_token_data :
    candle_disjunctive_case16594_complete_subtree_batch_token_data list;
  complete_subtree_batch_encoded_tokens : term;
  complete_subtree_batch_encoded_jobs : term;
  complete_subtree_batch_compute_theorem : thm;
};;

type candle_disjunctive_case16594_complete_subtree_batch_capture = {
  complete_subtree_batch_prepared : candle_q_dim_analytic_jet_prepared_six;
  complete_subtree_batch_segments :
    candle_disjunctive_case16594_complete_subtree_batch_segment_capture list;
};;

let candle_disjunctive_case16594_complete_subtree_batch_slot :
    candle_disjunctive_case16594_complete_subtree_batch_capture option ref =
  ref None;;

let candle_disjunctive_case16594_complete_subtree_batch_profile start phase =
  print_endline
    ("CANDLE_CERT_PROFILE" ^
     " lane=disjunctive-case16594-complete-subtree-batch" ^
     " phase=segment-" ^ string_of_int start ^ "-" ^ phase);;

let rec candle_disjunctive_case16594_complete_subtree_batch_compute
    prepared full_shape targets =
  match targets with
  | [] -> []
  | (start,cell_count,root_axis) :: remaining ->
      candle_disjunctive_case16594_complete_subtree_batch_profile
        start "preparation-begin";
      let shape =
        candle_disjunctive_case16594_complete_subtree_batch_find
          0 start cell_count full_shape in
      let cells =
        candle_disjunctive_case16594_complete_subtree_batch_cells shape in
      let token_data =
        candle_disjunctive_case16594_complete_subtree_batch_tokens shape in
      let actual_axis =
        match shape with
        | Candle_disjunctive_case16594_variable_axis_node (axis,_,_) -> axis
        | Candle_disjunctive_case16594_variable_axis_leaf _ -> 0 in
      if length cells <> cell_count ||
         length token_data <> 2 * cell_count - 1 ||
         actual_axis <> root_axis then
        failwith "case16594 complete subtree batch: selection drift";
      let encoded_tokens =
        candle_q_dim_stable_program_cval_list
          (map
            candle_disjunctive_case16594_complete_subtree_batch_encode_token
            token_data) in
      let encoded_jobs =
        candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
          cells in
      let call =
        list_mk_comb
          (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
           [prepared.program_representation_term;`Cexp_num 6`;
            encoded_tokens;encoded_jobs]) in
      candle_disjunctive_case16594_complete_subtree_batch_profile
        start "preparation-end";
      candle_disjunctive_case16594_complete_subtree_batch_profile
        start "kernel-compute-begin";
      let theorem =
        candle_q_dim_analytic_jet_compute
          (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
          call in
      candle_disjunctive_case16594_complete_subtree_batch_profile
        start "kernel-compute-end";
      let numerical,topology =
        candle_q_dim_stable_program_dest_cval_pair
          "case16594 complete subtree batch result" (rand (concl theorem)) in
      let topology_success,topology_payload =
        candle_q_dim_stable_program_dest_cval_pair
          "case16594 complete subtree batch topology" topology in
      let remaining_jobs,final_stack =
        candle_q_dim_stable_program_dest_cval_pair
          "case16594 complete subtree batch payload" topology_payload in
      let active_roots =
        candle_disjunctive_case16594_complete_subtree_batch_stack_length
          final_stack in
      if hyp theorem <> [] ||
         not (aconv (lhand (concl theorem)) call) ||
         not (aconv numerical `Cexp_num 1`) ||
         not (aconv topology_success `Cexp_num 1`) ||
         not (aconv remaining_jobs `Cexp_num 0`) || active_roots <> 1 then
        failwith "case16594 complete subtree batch: verdict mismatch";
      print_endline
        ("CANDLE_CV_CASE16594_COMPLETE_SUBTREE_BATCH_SEGMENT_RESULT" ^
         " start=" ^ string_of_int start ^
         " numerical_cells=" ^ string_of_int cell_count ^
         " token_items=" ^ string_of_int (length token_data) ^
         " root_axis=" ^ string_of_int root_axis ^
         " active_roots=1 assumptions=0");
      ({complete_subtree_batch_start = start;
        complete_subtree_batch_cells = cell_count;
        complete_subtree_batch_root_axis = root_axis;
        complete_subtree_batch_token_data = token_data;
        complete_subtree_batch_encoded_tokens = encoded_tokens;
        complete_subtree_batch_encoded_jobs = encoded_jobs;
        complete_subtree_batch_compute_theorem = theorem}) ::
      candle_disjunctive_case16594_complete_subtree_batch_compute
        prepared full_shape remaining;;

let _ =
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let segments =
    candle_disjunctive_case16594_complete_subtree_batch_compute
      prepared (candle_disjunctive_case16594_variable_axis_plan ())
      [(84,16,1);(466,16,3);(603,16,5);(801,16,5)] in
  if length segments <> 4 then
    failwith "case16594 complete subtree batch: segment count";
  candle_disjunctive_case16594_complete_subtree_batch_slot :=
    Some
      ({complete_subtree_batch_prepared = prepared;
        complete_subtree_batch_segments = segments});
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_SUBTREE_BATCH_CAPTURE_OK DEVELOPMENT_NON_RELEASE segments=4 numerical_cells=64 active_roots=4 assumptions=0";;

let candle_disjunctive_case16594_complete_subtree_batch_precomputed () =
  match !candle_disjunctive_case16594_complete_subtree_batch_slot with
  | Some captured -> captured
  | None -> failwith "case16594 complete subtree batch: unavailable";;

end;;
