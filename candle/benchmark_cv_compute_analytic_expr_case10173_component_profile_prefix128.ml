(* ========================================================================== *)
(* Numerical/topology timing split for the genuine case-10173 prefix.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This diagnostic evaluates the two existing   *)
(* components separately and requires their closed results to reconstruct   *)
(* the existing combined result exactly.  It changes no checker definition. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_component_profile_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let rec candle_case10173_component_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 component prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_component_cval_take (count - 1) tail);;

let rec candle_case10173_component_prefix_tokens leaves reversed items =
  if leaves = 0 then rev reversed else
  match items with
  | [] -> failwith "case10173 component prefix: short topology"
  | token :: remaining ->
      (match token with
       | Candle_case10173_complete_leaf ->
           candle_case10173_component_prefix_tokens
             (leaves - 1) (token :: reversed) remaining
       | Candle_case10173_complete_glue _ ->
           candle_case10173_component_prefix_tokens
             leaves (token :: reversed) remaining);;

let candle_case10173_component_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-component-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let token_data =
    candle_case10173_component_prefix_tokens 128 []
      (candle_case10173_complete_token_data ()) in
  if length token_data <> 250 then
    failwith "case10173 component prefix: topology drift";
  let encoded_jobs =
    candle_case10173_component_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let encoded_tokens =
    candle_case10173_component_cval_take (length token_data)
      captured.case10173_complete_encoded_tokens in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let combined_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [source_program;`Cexp_num 6`;encoded_tokens;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-combined-compute-begin";
  let combined =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      combined_call in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-combined-compute-end";
  let numerical_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [source_program;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-numerical-compute-begin";
  let numerical =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs numerical_call in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-numerical-compute-end";
  let topology_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;encoded_jobs;`Cexp_num 0`]) in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-topology-compute-begin";
  let topology =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      topology_call in
  candle_q_dim_analytic_jet_profile_event
    "component-prefix128-topology-compute-end";
  let expected_combined =
    candle_q_dim_stable_program_cval_pair
      (rand (concl numerical)) (rand (concl topology)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 component topology" (rand (concl topology)) in
  let remaining_jobs,_ =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 component topology payload" topology_payload in
  let axioms_after = axioms () in
  if not (candle_case10173_component_validate combined_call combined) ||
     not (candle_case10173_component_validate numerical_call numerical) ||
     not (candle_case10173_component_validate topology_call topology) ||
     not (aconv (rand (concl combined)) expected_combined) ||
     not (aconv (rand (concl numerical)) `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 component prefix: result mismatch";
  print_endline
    "CANDLE_CV_CASE10173_COMPONENT_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 token_items=250 matched=1 assumptions=0 axiom_growth=0";;

end;;
