(* ========================================================================== *)
(* Compute the complete genuine case-16594 certificate in one lean call.     *)
(*                                                                            *)
(* All 875 numerical cells and all 1,749 authentic postfix topology tokens   *)
(* remain cval data.  The closed compute theorem is retained for a late       *)
(* general-theorem handoff after the proof stack is loaded.                   *)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

type candle_disjunctive_case16594_complete_full_token_data =
  | Candle_disjunctive_case16594_complete_full_leaf
  | Candle_disjunctive_case16594_complete_full_glue of int;;

type candle_disjunctive_case16594_complete_full_task =
  | Candle_disjunctive_case16594_complete_full_visit of
      candle_disjunctive_case16594_variable_axis_tree_shape
  | Candle_disjunctive_case16594_complete_full_emit_glue of int;;

let rec candle_disjunctive_case16594_complete_full_traverse
    tasks reversed_cells reversed_tokens leaf_count glue_count =
  match tasks with
  | [] -> rev reversed_cells,rev reversed_tokens,leaf_count,glue_count
  | Candle_disjunctive_case16594_complete_full_visit shape :: remaining ->
      (match shape with
       | Candle_disjunctive_case16594_variable_axis_leaf cell ->
           candle_disjunctive_case16594_complete_full_traverse remaining
             (cell :: reversed_cells)
             (Candle_disjunctive_case16594_complete_full_leaf ::
               reversed_tokens)
             (leaf_count + 1) glue_count
       | Candle_disjunctive_case16594_variable_axis_node (axis,left,right) ->
           candle_disjunctive_case16594_complete_full_traverse
             (Candle_disjunctive_case16594_complete_full_visit left ::
              Candle_disjunctive_case16594_complete_full_visit right ::
              Candle_disjunctive_case16594_complete_full_emit_glue axis ::
              remaining)
             reversed_cells reversed_tokens leaf_count glue_count)
  | Candle_disjunctive_case16594_complete_full_emit_glue axis :: remaining ->
      candle_disjunctive_case16594_complete_full_traverse remaining
        reversed_cells
        (Candle_disjunctive_case16594_complete_full_glue axis ::
          reversed_tokens)
        leaf_count (glue_count + 1);;

let candle_disjunctive_case16594_complete_full_encode_token = function
  | Candle_disjunctive_case16594_complete_full_leaf -> `Cexp_num 0`
  | Candle_disjunctive_case16594_complete_full_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let rec candle_disjunctive_case16594_complete_full_stack_length encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete full stack" encoded in
    1 + candle_disjunctive_case16594_complete_full_stack_length tail;;

type candle_disjunctive_case16594_complete_full_capture = {
  complete_full_prepared : candle_q_dim_analytic_jet_prepared_six;
  complete_full_token_data :
    candle_disjunctive_case16594_complete_full_token_data list;
  complete_full_encoded_tokens : term;
  complete_full_encoded_jobs : term;
  complete_full_compute_theorem : thm;
};;

let candle_disjunctive_case16594_complete_full_slot :
    candle_disjunctive_case16594_complete_full_capture option ref =
  ref None;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-complete-full-precomputed" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-preparation-begin";
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells,token_data,leaf_count,glue_count =
    candle_disjunctive_case16594_complete_full_traverse
      [Candle_disjunctive_case16594_complete_full_visit
        (candle_disjunctive_case16594_variable_axis_plan ())]
      [] [] 0 0 in
  if leaf_count <> 875 || glue_count <> 874 || length cells <> 875 ||
     length token_data <> 1749 then
    failwith "case16594 complete full capture: plan shape mismatch";
  let encoded_tokens =
    candle_q_dim_stable_program_cval_list
      (map candle_disjunctive_case16594_complete_full_encode_token
        token_data) in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      call in
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-kernel-compute-end";
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete full result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete full topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete full payload" topology_payload in
  let active_roots =
    candle_disjunctive_case16594_complete_full_stack_length final_stack in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) || active_roots <> 1 then
    failwith "case16594 complete full capture: verdict mismatch";
  candle_disjunctive_case16594_complete_full_slot :=
    Some
      ({complete_full_prepared = prepared;
        complete_full_token_data = token_data;
        complete_full_encoded_tokens = encoded_tokens;
        complete_full_encoded_jobs = encoded_jobs;
        complete_full_compute_theorem = theorem});
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_FULL_CAPTURE_OK DEVELOPMENT_NON_RELEASE authenticated_leaves=860 numerical_cells=875 token_items=1749 active_roots=1 remaining_jobs=0 assumptions=0";;

let candle_disjunctive_case16594_complete_full_precomputed () =
  match !candle_disjunctive_case16594_complete_full_slot with
  | Some captured -> captured
  | None -> failwith "case16594 complete full capture: unavailable";;

end;;
