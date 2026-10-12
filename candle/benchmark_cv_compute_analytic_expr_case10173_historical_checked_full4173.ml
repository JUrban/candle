(* ========================================================================== *)
(* Checked historical-dihedral splice on all 4,173 genuine case-10173 jobs. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The auxiliary roots are untrusted captured    *)
(* data.  The reflected checker recomputes their radicands from every         *)
(* authenticated job box and proves all 16,692 enclosures before accepting.  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_checked_full4173 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128;;

let candle_case10173_hist_checked_full_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_full4173.tsv";;

let candle_case10173_hist_checked_full_roots =
  print_endline "CANDLE_HIST_CHECKED_FULL_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_hist_checked_full_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_hist_splice_record index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 4173 then
        failwith "case10173 checked full: fixture record-count drift";
      candle_case10173_hist_splice_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_HIST_CHECKED_FULL_FIXTURE_LOAD_END records=4173";
  result;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-historical-checked-full4173" ^
       " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  if not (candle_case10173_hist_splice_validate_source source_program) then
    failwith "case10173 checked full: source segment drift";
  let call = list_mk_comb
    (`candle_cv_case10173_hist_checked_raw_jobs_check`,
     [source_program;captured.case10173_complete_encoded_jobs;
      candle_case10173_hist_checked_full_roots]) in
  candle_q_dim_analytic_jet_profile_event "checked-compute-begin";
  let theorem = candle_q_dim_analytic_jet_compute
    candle_cv_case10173_hist_checked_program_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "checked-compute-end";
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 checked full: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_CHECKED_FULL4173_OK DEVELOPMENT_NON_RELEASE cells=4173 result=1 authenticated_aux_roots=16692 assumptions=0 axiom_growth=0";;

end;;
