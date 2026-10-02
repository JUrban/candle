(* ========================================================================== *)
(* Compute the genuine prefix-16 numerical and topology verdict before       *)
(* loading the complete-checker soundness and handoff layers.                 *)
(*                                                                            *)
(* The axis tree is untrusted preparation data.  This unit emits its compact *)
(* postfix token segment directly as cval data; the late handoff independently*)
(* reifies the same segment into logical tokens and checks the exact encoding. *)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_prefix16_precomputed_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

type candle_disjunctive_case16594_complete_prefix16_token_data =
  | Candle_disjunctive_case16594_complete_prefix16_leaf
  | Candle_disjunctive_case16594_complete_prefix16_glue of int;;

type candle_disjunctive_case16594_complete_prefix16_token_task =
  | Candle_disjunctive_case16594_complete_prefix16_visit of
      candle_disjunctive_case16594_variable_axis_tree_shape
  | Candle_disjunctive_case16594_complete_prefix16_emit_glue of int;;

let rec candle_disjunctive_case16594_complete_prefix16_token_run
    tasks reversed =
  match tasks with
  | [] -> rev reversed
  | Candle_disjunctive_case16594_complete_prefix16_visit shape :: remaining ->
      (match shape with
       | Candle_disjunctive_case16594_variable_axis_leaf _ ->
           candle_disjunctive_case16594_complete_prefix16_token_run remaining
             (Candle_disjunctive_case16594_complete_prefix16_leaf :: reversed)
       | Candle_disjunctive_case16594_variable_axis_node (axis,left,right) ->
           candle_disjunctive_case16594_complete_prefix16_token_run
             (Candle_disjunctive_case16594_complete_prefix16_visit left ::
              Candle_disjunctive_case16594_complete_prefix16_visit right ::
              Candle_disjunctive_case16594_complete_prefix16_emit_glue axis ::
              remaining)
             reversed)
  | Candle_disjunctive_case16594_complete_prefix16_emit_glue axis ::
      remaining ->
      candle_disjunctive_case16594_complete_prefix16_token_run remaining
        (Candle_disjunctive_case16594_complete_prefix16_glue axis :: reversed);;

let rec candle_disjunctive_case16594_complete_prefix16_take_tokens
    leaves reversed = function
  | [] ->
      if leaves = 0 then rev reversed,[]
      else failwith "case16594 complete prefix16 capture: short token plan"
  | token :: remaining ->
      (match token with
       | Candle_disjunctive_case16594_complete_prefix16_leaf ->
           if leaves = 0 then rev reversed,token :: remaining
           else
             candle_disjunctive_case16594_complete_prefix16_take_tokens
               (leaves - 1) (token :: reversed) remaining
       | Candle_disjunctive_case16594_complete_prefix16_glue _ ->
           candle_disjunctive_case16594_complete_prefix16_take_tokens
             leaves (token :: reversed) remaining);;

let rec candle_disjunctive_case16594_complete_prefix16_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 complete prefix16 capture: short cell plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_complete_prefix16_take (count - 1) tail;;

let candle_disjunctive_case16594_complete_prefix16_encode_token = function
  | Candle_disjunctive_case16594_complete_prefix16_leaf -> `Cexp_num 0`
  | Candle_disjunctive_case16594_complete_prefix16_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let rec candle_disjunctive_case16594_complete_prefix16_stack_length encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete prefix16 capture stack" encoded in
    1 + candle_disjunctive_case16594_complete_prefix16_stack_length tail;;

type candle_disjunctive_case16594_complete_prefix16_precomputed_capture = {
  complete_prefix16_precomputed_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  complete_prefix16_precomputed_token_data :
    candle_disjunctive_case16594_complete_prefix16_token_data list;
  complete_prefix16_precomputed_encoded_tokens : term;
  complete_prefix16_precomputed_encoded_jobs : term;
  complete_prefix16_precomputed_theorem : thm;
  complete_prefix16_precomputed_active_roots : int;
};;

let candle_disjunctive_case16594_complete_prefix16_precomputed_slot :
    candle_disjunctive_case16594_complete_prefix16_precomputed_capture option ref =
  ref None;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-complete-prefix16-precomputed" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event
    "complete-prefix16-precomputed-preparation-begin";
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_complete_prefix16_take 16
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let all_token_data =
    candle_disjunctive_case16594_complete_prefix16_token_run
      [Candle_disjunctive_case16594_complete_prefix16_visit
        (candle_disjunctive_case16594_variable_axis_plan ())]
      [] in
  let token_data,remaining_token_data =
    candle_disjunctive_case16594_complete_prefix16_take_tokens
      16 [] all_token_data in
  if length all_token_data <> 1749 || length token_data <> 29 ||
     remaining_token_data = [] then
    failwith "case16594 complete prefix16 capture: token shape mismatch";
  let encoded_tokens =
    candle_q_dim_stable_program_cval_list
      (map candle_disjunctive_case16594_complete_prefix16_encode_token
        token_data) in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event
    "complete-prefix16-precomputed-preparation-end";
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "complete-prefix16-precomputed-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      call in
  candle_q_dim_analytic_jet_profile_event
    "complete-prefix16-precomputed-kernel-compute-end";
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete prefix16 capture result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete prefix16 capture topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 complete prefix16 capture payload" topology_payload in
  let active_roots =
    candle_disjunctive_case16594_complete_prefix16_stack_length final_stack in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) || active_roots <> 3 then
    failwith "case16594 complete prefix16 capture: verdict mismatch";
  candle_disjunctive_case16594_complete_prefix16_precomputed_slot :=
    Some
      ({complete_prefix16_precomputed_prepared = prepared;
        complete_prefix16_precomputed_token_data = token_data;
        complete_prefix16_precomputed_encoded_tokens = encoded_tokens;
        complete_prefix16_precomputed_encoded_jobs = encoded_jobs;
        complete_prefix16_precomputed_theorem = theorem;
        complete_prefix16_precomputed_active_roots = active_roots});
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_PREFIX16_PRECOMPUTED_CAPTURE_RESULT numerical_cells=16 token_items=29 active_roots=3 assumptions=0";
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_PREFIX16_PRECOMPUTED_CAPTURE_OK DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_case16594_complete_prefix16_precomputed () =
  match !candle_disjunctive_case16594_complete_prefix16_precomputed_slot with
  | Some captured -> captured
  | None ->
      failwith "case16594 complete prefix16 precomputed capture: unavailable";;

end;;
