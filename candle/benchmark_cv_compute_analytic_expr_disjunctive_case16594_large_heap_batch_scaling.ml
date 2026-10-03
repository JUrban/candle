(* ========================================================================== *)
(* Large-heap scaling for the genuine case-16594 raw numerical checker.      *)
(*                                                                            *)
(* The stable source program and complete 875-cell plan are already resident *)
(* in the lean checkpoint.  Each trial selects an exact prefix, encodes its   *)
(* changing certificate data, and computes one closed acceptance verdict.    *)
(* No result theorem or expanded certificate is retained between trials.     *)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_large_heap_batch_scaling = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_disjunctive_case16594_large_heap_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 large-heap scaling: short plan"
  | head :: tail ->
      head :: candle_disjunctive_case16594_large_heap_take (count - 1) tail;;

let candle_disjunctive_case16594_large_heap_marker count phase =
  candle_q_dim_analytic_jet_profile_event
    ("large-heap-prefix-" ^ string_of_int count ^ "-" ^ phase);;

let candle_disjunctive_case16594_large_heap_run count =
  if count <= 0 || count > 875 then
    failwith "case16594 large-heap scaling: invalid count";
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  candle_disjunctive_case16594_large_heap_marker count "encoding-begin";
  let cells =
    candle_disjunctive_case16594_large_heap_take count
      candle_disjunctive_case16594_variable_raw_plan_cells in
  if length cells <> count then
    failwith "case16594 large-heap scaling: prefix shape mismatch";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_disjunctive_case16594_large_heap_marker count "encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_disjunctive_case16594_large_heap_marker count
    "kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs call in
  candle_disjunctive_case16594_large_heap_marker count
    "kernel-compute-end";
  if hyp theorem <> [] ||
     not (aconv (concl theorem) (mk_eq (call,`Cexp_num 1`))) then
    failwith "case16594 large-heap scaling: verdict mismatch";
  print_endline
    ("CANDLE_CV_CASE16594_LARGE_HEAP_BATCH_RESULT" ^
     " cells=" ^ string_of_int count ^
     " accepted=1 assumptions=0 retained_results=0");;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-large-heap-batch-scaling" ^
         " phase=" ^ event));;

let _ = candle_disjunctive_case16594_large_heap_run 1;;
let _ = candle_disjunctive_case16594_large_heap_run 8;;
let _ = candle_disjunctive_case16594_large_heap_run 32;;
let _ = candle_disjunctive_case16594_large_heap_run 128;;

let _ =
  print_endline
    "CANDLE_CV_CASE16594_LARGE_HEAP_BATCH_SCALING_OK DEVELOPMENT_NON_RELEASE batches=1,8,32,128 accepted=4 stable_programs=1 retained_results=0";;

end;;
