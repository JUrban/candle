(* ========================================================================== *)
(* Proof-producing adapter for canonical raw variable-certificate batches.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

type candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six = {
  variable_raw_prepared_source : candle_q_dim_analytic_jet_prepared_six;
  variable_raw_encoded_jobs_term : term;
  variable_raw_decoded_jobs_term : term;
  variable_raw_representation_theorem : thm;
  variable_raw_accept_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
    intervals =
  candle_q_dim_stable_program_encode_intervals intervals;;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cell_six
    cell =
  let stable = cell.variable_batch_stable_cell in
  if length stable.stable_batch_lower <> 6 ||
     length stable.stable_batch_upper <> 6 then
    failwith "fixed outer variable raw prover: expected six coordinates";
  let boxes =
    candle_poly_fixture_q_boxes
      stable.stable_batch_lower stable.stable_batch_upper in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
      cell.variable_batch_box_intervals)
    (candle_q_dim_stable_program_cval_pair
      (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
        stable.stable_batch_center_intervals)
      (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
        (dest_list boxes)));;

let rec candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six =
  function
  | [] -> `Cexp_num 0`
  | cell :: remaining ->
      candle_q_dim_stable_program_cval_pair
        (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cell_six
          cell)
        (candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
          remaining);;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_encoded_six
    prepared encoded_jobs =
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-proof-preparation-begin";
  let decoded_jobs =
    mk_comb (`candle_cv_fso_variable_jobs_decode`,encoded_jobs) in
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-proof-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "fixed outer variable raw prover: raw batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-batch-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fso_variable_raw_jobs_check`)
      [source_program_encoding;REFL encoded_jobs] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let representation_theorem =
    MATCH_MP
      (SPECL
        [encoded_jobs;prepared.expression_term]
        candle_cv_fso_variable_raw_jobs_check_representation_accept)
      abstract_compute in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [encoded_jobs;prepared.expression_term]
        candle_cv_fso_variable_raw_jobs_check_accept)
      abstract_compute in
  let accept_operator,accept_arguments =
    strip_comb (concl accept_theorem) in
  if hyp accept_theorem <> [] ||
     not
       (aconv accept_operator
          `candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`) ||
     (match accept_arguments with
      | [actual_source;actual_jobs] ->
          not
            (aconv actual_source prepared.expression_term &&
             aconv actual_jobs decoded_jobs)
      | _ -> true) then
    failwith "fixed outer variable raw prover: acceptance mismatch";
  let expected_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       encoded_jobs) in
  if hyp representation_theorem <> [] ||
     not (aconv (concl representation_theorem) expected_representation) then
    failwith "fixed outer variable raw prover: representation mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certified-taylor-batch-handoff-end";
  {variable_raw_prepared_source = prepared;
   variable_raw_encoded_jobs_term = encoded_jobs;
   variable_raw_decoded_jobs_term = decoded_jobs;
   variable_raw_representation_theorem = representation_theorem;
   variable_raw_accept_theorem = accept_theorem};;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
    prepared cells =
  if cells = [] then
    failwith "fixed outer variable raw prover: empty batch";
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certificate-encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event
    "variable-raw-certificate-encoding-end";
  candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_encoded_six
    prepared encoded_jobs;;

end;;
