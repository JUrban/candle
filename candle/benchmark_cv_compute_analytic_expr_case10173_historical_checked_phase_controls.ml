(* ========================================================================== *)
(* Phase controls for the complete case-10173 historical checked batch.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The full-input control forces Kernel.compute  *)
(* to decode the exact source, 4,173 jobs, and four-root records, but its     *)
(* checked function returns immediately.  The empty-job call uses the exact  *)
(* complete checker and equation set with only the shared source argument.   *)
(* Together they separate fixed evaluator/equation setup, input decoding,    *)
(* and recurring numerical checking from fixture construction outside the    *)
(* kernel call.                                                               *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_checked_phase_controls = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128;;

let candle_case10173_hist_phase_control_def = new_definition
 `candle_case10173_hist_phase_control
      (source_program:cval) (encoded_jobs:cval) (roots:cval) =
    Cexp_num 1`;;

let candle_case10173_hist_phase_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_full4173.tsv";;

let candle_case10173_hist_phase_roots =
  print_endline "CANDLE_HIST_PHASE_FULL_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_hist_phase_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_hist_splice_record index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 4173 then
        failwith "case10173 checked phase: fixture record-count drift";
      candle_case10173_hist_splice_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_HIST_PHASE_FULL_FIXTURE_LOAD_END records=4173";
  result;;

let _ =
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  if not (candle_case10173_hist_splice_validate_source source_program) then
    failwith "case10173 checked phase: source segment drift";
  let control_call = list_mk_comb
    (`candle_case10173_hist_phase_control`,
     [source_program;captured.case10173_complete_encoded_jobs;
      candle_case10173_hist_phase_roots]) in
  let control_eqs =
    SPEC_ALL candle_case10173_hist_phase_control_def ::
    candle_cv_case10173_hist_checked_program_compute_eqs in
  print_endline "CANDLE_HIST_PHASE_CONTROL_COMPUTE_BEGIN";
  let control_theorem = candle_q_dim_analytic_jet_compute
    control_eqs control_call in
  print_endline "CANDLE_HIST_PHASE_CONTROL_COMPUTE_END";
  let empty_call = list_mk_comb
    (`candle_cv_case10173_hist_checked_raw_jobs_check`,
     [source_program;`Cexp_num 0`;`Cexp_num 0`]) in
  print_endline "CANDLE_HIST_PHASE_EMPTY_COMPUTE_BEGIN";
  let empty_theorem = candle_q_dim_analytic_jet_compute
    candle_cv_case10173_hist_checked_program_compute_eqs empty_call in
  print_endline "CANDLE_HIST_PHASE_EMPTY_COMPUTE_END";
  let full_call = list_mk_comb
    (`candle_cv_case10173_hist_checked_raw_jobs_check`,
     [source_program;captured.case10173_complete_encoded_jobs;
      candle_case10173_hist_phase_roots]) in
  print_endline "CANDLE_HIST_PHASE_FULL_COMPUTE_BEGIN";
  let full_theorem = candle_q_dim_analytic_jet_compute
    candle_cv_case10173_hist_checked_program_compute_eqs full_call in
  print_endline "CANDLE_HIST_PHASE_FULL_COMPUTE_END";
  if hyp control_theorem <> [] || hyp empty_theorem <> [] ||
     hyp full_theorem <> [] ||
     not (aconv (lhand (concl control_theorem)) control_call) ||
     not (aconv (rand (concl control_theorem)) `Cexp_num 1`) ||
     not (aconv (lhand (concl empty_theorem)) empty_call) ||
     not (aconv (rand (concl empty_theorem)) `Cexp_num 1`) ||
     not (aconv (lhand (concl full_theorem)) full_call) ||
     not (aconv (rand (concl full_theorem)) `Cexp_num 1`) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 checked phase: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_PHASE_CONTROLS_OK DEVELOPMENT_NON_RELEASE cells=4173 result=1 assumptions=0 axiom_growth=0";;

end;;
