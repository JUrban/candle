(* ========================================================================== *)
(* Checked historical-dihedral splice on 128 genuine case-10173 jobs.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This reuses the unchanged captured jobs and   *)
(* auxiliary-root fixture, but runs the fail-closed checker which recomputes  *)
(* every radicand and authenticates every supplied root enclosure.            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_checked_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-historical-checked-prefix128" ^
       " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  if not (candle_case10173_hist_splice_validate_source source_program) then
    failwith "case10173 checked historical splice: source segment drift";
  let encoded_jobs = candle_case10173_hist_splice_take 128
    captured.case10173_complete_encoded_jobs in
  let call = list_mk_comb
    (`candle_cv_case10173_hist_checked_raw_jobs_check`,
     [source_program;encoded_jobs;candle_case10173_hist_splice_roots]) in
  candle_q_dim_analytic_jet_profile_event "checked-compute-begin";
  let theorem = candle_q_dim_analytic_jet_compute
    candle_cv_case10173_hist_checked_program_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "checked-compute-end";
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 checked historical splice: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 result=1 authenticated_aux_roots=512 assumptions=0 axiom_growth=0";;

end;;
