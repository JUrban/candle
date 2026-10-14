(* ========================================================================== *)
(* Final registered-result handoff to the literal original case-10173 goal.  *)
(*                                                                            *)
(* The only computational premise supplied by callers is the closed          *)
(* registered numerical acceptance.  Compact topology, root-domain identity, *)
(* and the already-proved universal analytic/source bridge finish the proof.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_registered_combine.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_registered_topology_prove.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_registered_domain_prove.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_ledger_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_registered_original_prove = struct

open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_registered_combine;;
open Candle_cv_analytic_expr_case10173_historical_registered_topology_prove;;
open Candle_cv_analytic_expr_case10173_historical_registered_domain_prove;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_ledger_sound;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture;;

let candle_case10173_historical_registered_original_prove
    acceptance topology_capture topology_result =
  if hyp acceptance.registered_acceptance_jobs_pass <> [] ||
     hyp topology_result.registered_topology_run_theorem <> [] then
    failwith "case10173 registered original prove: premise assumptions";
  let domain_identity =
    candle_case10173_historical_registered_domain_prove
      topology_result.registered_topology_root_boxes in
  let soundness =
    ISPECL
      [acceptance.registered_acceptance_decoded_jobs;
       topology_capture.registered_topology_tokens;
       `ARB:real^6`;
       topology_result.registered_topology_root_boxes]
      candle_case10173_hist_authenticated_ledger_original_sound in
  let premise =
    CONJ acceptance.registered_acceptance_jobs_pass
      (CONJ topology_result.registered_topology_run_theorem domain_identity) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "case10173 registered original prove: premise mismatch";
  let theorem = MATCH_MP soundness premise in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  if hyp theorem <> [] ||
     not (aconv (concl theorem) candle_case10173_analytic_target) ||
     digest <> "48c97d39af116042909b7896d0d83123"
  then failwith "case10173 registered original prove: final theorem drift";
  theorem;;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_ORIGINAL_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
