(* Logical compact-run handoff for the registered genuine case-10173 data. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_registered_topology_prove.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_topology_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound;;
open Candle_cv_analytic_expr_case10173_historical_registered_topology_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture;;

let _ =
  let axioms_before = axioms () in
  let ledger = candle_case10173_historical_registered_ledger_input () in
  let complete = candle_case10173_complete_capture () in
  let topology =
    candle_case10173_historical_registered_topology_capture () in
  let encoded_jobs = ledger.registered_ledger_full_encoded_jobs in
  if not (aconv encoded_jobs complete.case10173_complete_encoded_jobs) ||
     not
       (aconv
         topology.registered_topology_encoded_tokens
         complete.case10173_complete_encoded_tokens)
  then failwith "case10173 registered topology prove test: input drift";
  let prepared = complete.case10173_complete_prepared in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_COMPONENTS_BEGIN";
  let components =
    MATCH_MP
      (SPECL
        [prepared.program_representation_term;`Cexp_num 6`;
         topology.registered_topology_encoded_tokens;encoded_jobs;
         topology.registered_topology_encoded_root]
        candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_components)
      complete.case10173_complete_compute_theorem in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_COMPONENTS_END";
  let concrete_numerical = CONJUNCT1 components in
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fso_variable_raw_jobs_check`)
      [source_program_encoding;REFL encoded_jobs] in
  let abstract_numerical = TRANS call_encoding concrete_numerical in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_REPRESENTATION_BEGIN";
  let representation =
    MATCH_MP
      (SPECL [encoded_jobs;prepared.expression_term]
        candle_cv_fso_variable_raw_jobs_check_representation_accept)
      abstract_numerical in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_REPRESENTATION_END";
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_HANDOFF_BEGIN";
  let result =
    candle_case10173_historical_registered_topology_prove
      encoded_jobs representation topology in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_PROVE_HANDOFF_END";
  let axioms_after = axioms () in
  if hyp result.registered_topology_run_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 registered topology prove test: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_TOPOLOGY_PROVE_TEST_OK DEVELOPMENT_NON_RELEASE jobs=4173 tokens=8345 assumptions=0 axiom_growth=0 numerical_compute=0";;

end;;
