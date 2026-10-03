(* ========================================================================== *)
(* Matched canonical-guard benchmark on 128 genuine case-10173 cells.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established complete checker rebuilds    *)
(* the canonical raw job term and compares it with the input.  The already   *)
(* proved fast checker scans well-formedness directly.  Both calls below use *)
(* the exact same preserved jobs and topology prefix.                         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_fast.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_raw_fast_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_fast;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_fast_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_fast
        source_program tree_dim tokens encoded_jobs =
      Cexp_pair
        (candle_cv_fso_variable_raw_jobs_check_fast
          source_program encoded_jobs)
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
          tree_dim tokens encoded_jobs (Cexp_num 0))`;;

let candle_case10173_raw_fast_complete_compute_eqs () =
  union candle_cv_fso_variable_raw_fast_compute_eqs
    (union
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      [SPEC_ALL
        candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_fast_def]);;

let rec candle_case10173_raw_fast_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 raw-fast prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_raw_fast_cval_take (count - 1) tail);;

let rec candle_case10173_raw_fast_prefix_tokens leaves reversed items =
  if leaves = 0 then rev reversed else
  match items with
  | [] -> failwith "case10173 raw-fast prefix: short topology"
  | token :: remaining ->
      (match token with
       | Candle_case10173_complete_leaf ->
           candle_case10173_raw_fast_prefix_tokens
             (leaves - 1) (token :: reversed) remaining
       | Candle_case10173_complete_glue _ ->
           candle_case10173_raw_fast_prefix_tokens
             leaves (token :: reversed) remaining);;

let candle_case10173_raw_fast_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-raw-fast-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let token_data =
    candle_case10173_raw_fast_prefix_tokens 128 []
      (candle_case10173_complete_token_data ()) in
  if length token_data <> 250 then
    failwith "case10173 raw-fast prefix: topology drift";
  let encoded_jobs =
    candle_case10173_raw_fast_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let encoded_tokens =
    candle_case10173_raw_fast_cval_take (length token_data)
      captured.case10173_complete_encoded_tokens in
  let prepared = captured.case10173_complete_prepared in
  let arguments =
    [prepared.program_representation_term;
     `Cexp_num 6`;encoded_tokens;encoded_jobs] in
  let established_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       arguments) in
  candle_q_dim_analytic_jet_profile_event
    "raw-fast-prefix128-established-compute-begin";
  let established =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      established_call in
  candle_q_dim_analytic_jet_profile_event
    "raw-fast-prefix128-established-compute-end";
  let fast_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_fast`,
       arguments) in
  candle_q_dim_analytic_jet_profile_event
    "raw-fast-prefix128-direct-well-formed-compute-begin";
  let fast =
    candle_q_dim_analytic_jet_compute
      (candle_case10173_raw_fast_complete_compute_eqs ()) fast_call in
  candle_q_dim_analytic_jet_profile_event
    "raw-fast-prefix128-direct-well-formed-compute-end";
  let axioms_after = axioms () in
  if not (candle_case10173_raw_fast_validate established_call established) ||
     not (candle_case10173_raw_fast_validate fast_call fast) ||
     not (aconv (rand (concl established)) (rand (concl fast))) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 raw-fast prefix: result mismatch";
  print_endline
    "CANDLE_CV_CASE10173_RAW_FAST_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 token_items=250 matched=1 assumptions=0 axiom_growth=0";;

end;;
