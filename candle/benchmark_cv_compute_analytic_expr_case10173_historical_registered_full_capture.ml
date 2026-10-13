(* ========================================================================== *)
(* Exact complete historical case-10173 call for the fast kernel gate.        *)
(*                                                                            *)
(* This preserves the same 4,173 jobs, source program, auxiliary roots, and   *)
(* checked wrapper used by the measured full reflected run.                   *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_registered_hol4_export.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128;;

type candle_case10173_historical_registered_full_capture =
  thm list * term * thm;;

let candle_case10173_historical_registered_full_capture_state :
    candle_case10173_historical_registered_full_capture option ref = ref None;;

let candle_case10173_historical_registered_full_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_full4173.tsv";;

let candle_case10173_historical_registered_full_roots () =
  print_endline "CANDLE_REGISTERED_FULL_FIXTURE_LOAD_BEGIN";
  let channel =
    Stdlib.open_in candle_case10173_historical_registered_full_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_hist_splice_record index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 4173 then
        failwith "case10173 registered full: fixture record-count drift";
      candle_case10173_hist_splice_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_REGISTERED_FULL_FIXTURE_LOAD_END records=4173";
  result;;

let _ =
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  if not (candle_case10173_hist_splice_validate_source source_program) then
    failwith "case10173 registered full: source segment drift";
  let roots = candle_case10173_historical_registered_full_roots () in
  let call = list_mk_comb
    (`candle_cv_case10173_hist_checked_raw_jobs_check`,
     [source_program;captured.case10173_complete_encoded_jobs;roots]) in
  let equations = candle_registered_equation_slice
    candle_cv_case10173_hist_checked_program_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "registered-full-compute-begin";
  let theorem = Kernel.compute (COMPUTE_INIT_THMS,equations) call in
  candle_q_dim_analytic_jet_profile_event "registered-full-compute-end";
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 registered full: verdict mismatch";
  candle_case10173_historical_registered_full_capture_state :=
    Some (equations,call,theorem);
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_FULL_OK" ^
     " DEVELOPMENT_NON_RELEASE cells=4173 equations=" ^
     string_of_int (length equations) ^
     " assumptions=0 result=1 axiom_growth=0");;

let candle_case10173_historical_registered_full_capture () =
  match !candle_case10173_historical_registered_full_capture_state with
  | Some captured -> captured
  | None -> failwith "case10173 registered full: unavailable";;

end;;
