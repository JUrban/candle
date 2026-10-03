(* ========================================================================== *)
(* One-verdict proved fixed-nonlinear capture for genuine case 10173.         *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_case10173_fixed_nonlinear_complete_compute_state :
    thm option ref = ref None;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-fixed-nonlinear-complete" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let prepared = captured.case10173_complete_prepared in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        captured.case10173_complete_encoded_tokens;
        captured.case10173_complete_encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs
        ())
      call in
  candle_q_dim_analytic_jet_profile_event
    "complete-certificate-kernel-compute-end";
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 fixed nonlinear complete result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 fixed nonlinear complete topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 fixed nonlinear complete payload" topology_payload in
  let active_roots = candle_case10173_complete_stack_length final_stack in
  let axioms_after = axioms () in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) || active_roots <> 1 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 fixed nonlinear complete: verdict mismatch";
  candle_case10173_fixed_nonlinear_complete_compute_state := Some theorem;
  print_endline
    "CANDLE_CV_CASE10173_FIXED_NONLINEAR_COMPLETE_CAPTURE_OK DEVELOPMENT_NON_RELEASE roots=3305 numerical_cells=4173 token_items=8345 active_roots=1 remaining_jobs=0 assumptions=0 axiom_growth=0";;

let candle_case10173_fixed_nonlinear_complete_compute () =
  match !candle_case10173_fixed_nonlinear_complete_compute_state with
  | Some theorem -> theorem
  | None -> failwith "case10173 fixed nonlinear complete: unavailable";;

end;;
