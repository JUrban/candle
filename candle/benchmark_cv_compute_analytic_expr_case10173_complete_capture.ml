(* ========================================================================== *)
(* One-verdict capture for the complete genuine case-10173 certificate.      *)
(*                                                                            *)
(* All 4,173 numerical cells and 8,345 postfix topology tokens remain raw    *)
(* cval data during evaluation.  The closed compute theorem is retained for  *)
(* a separately measured general-theorem/source handoff.                     *)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_topology.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_complete_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;

let candle_case10173_complete_encode_token = function
  | Candle_case10173_complete_leaf -> `Cexp_num 0`
  | Candle_case10173_complete_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let rec candle_case10173_complete_stack_length encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case10173 complete stack" encoded in
    1 + candle_case10173_complete_stack_length tail;;

type candle_case10173_complete_capture = {
  case10173_complete_prepared : candle_q_dim_analytic_jet_prepared_six;
  case10173_complete_encoded_tokens : term;
  case10173_complete_encoded_jobs : term;
  case10173_complete_compute_theorem : thm;
};;

let candle_case10173_complete_capture_state :
    candle_case10173_complete_capture option ref = ref None;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-complete-capture" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let plan = candle_case10173_variable_raw_plan () in
  let token_data = candle_case10173_complete_token_data () in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-job-encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      plan.case10173_variable_raw_plan_cells in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-job-encoding-end";
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-token-encoding-begin";
  let encoded_tokens =
    candle_q_dim_stable_program_cval_list
      (map candle_case10173_complete_encode_token token_data) in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-token-encoding-end";
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-call-construction-begin";
  let prepared = plan.case10173_variable_raw_plan_prepared in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-call-construction-end";
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      call in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-kernel-compute-end";
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 complete result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 complete topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 complete payload" topology_payload in
  let active_roots = candle_case10173_complete_stack_length final_stack in
  let axioms_after = axioms () in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) || active_roots <> 1 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 complete capture: verdict mismatch";
  let captured = {
    case10173_complete_prepared = prepared;
    case10173_complete_encoded_tokens = encoded_tokens;
    case10173_complete_encoded_jobs = encoded_jobs;
    case10173_complete_compute_theorem = theorem;
  } in
  candle_case10173_complete_capture_state := Some captured;
  print_endline
    "CANDLE_CV_CASE10173_COMPLETE_CAPTURE_OK DEVELOPMENT_NON_RELEASE roots=3305 numerical_cells=4173 token_items=8345 active_roots=1 remaining_jobs=0 assumptions=0 axiom_growth=0";;

let candle_case10173_complete_capture () =
  match !candle_case10173_complete_capture_state with
  | Some captured -> captured
  | None -> failwith "case10173 complete capture: unavailable";;

end;;
