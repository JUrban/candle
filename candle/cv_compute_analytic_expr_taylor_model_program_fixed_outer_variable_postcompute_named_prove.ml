(* ========================================================================== *)
(* Compact, definition-backed handoff after a raw numerical computation.      *)
(*                                                                            *)
(* The large certificate value is deliberately absent from the kernel state  *)
(* until Kernel.compute has accepted it.  A fresh definition is then used     *)
(* once to transport the computed verdict to a small named source node.       *)
(* The raw value remains available separately for later computed consumers,   *)
(* so they do not repeatedly unfold the definition during evaluation.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support;;

type candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_result_six = {
  variable_postcompute_named_raw_result :
    candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six;
  variable_postcompute_named_compute_encoded_jobs_term : term;
  variable_postcompute_named_jobs_definition : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_handoff_computed_six
    prepared requested_named_jobs encoded_jobs concrete_compute =
  if not (type_of requested_named_jobs = `:cval`) then
    failwith "fixed outer postcompute named prover: expected cval name";
  let concrete_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  let expected_concrete_compute =
    mk_eq (concrete_call,`Cexp_num 1`) in
  if hyp concrete_compute <> [] ||
     not (aconv (concl concrete_compute) expected_concrete_compute) then
    failwith "fixed outer postcompute named prover: computed theorem mismatch";
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-definition-begin";
  let jobs_definition =
    new_definition (mk_eq (requested_named_jobs,encoded_jobs)) in
  let named_jobs = lhand (concl jobs_definition) in
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-definition-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fso_variable_raw_jobs_check`)
      [source_program_encoding;jobs_definition] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let decoded_jobs =
    mk_comb (`candle_cv_fso_variable_jobs_decode`,named_jobs) in
  let representation_theorem =
    MATCH_MP
      (SPECL
        [named_jobs;prepared.expression_term]
        candle_cv_fso_variable_raw_jobs_check_representation_accept)
      abstract_compute in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [named_jobs;prepared.expression_term]
        candle_cv_fso_variable_raw_jobs_check_accept)
      abstract_compute in
  let expected_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       named_jobs) in
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;decoded_jobs]) in
  if hyp jobs_definition <> [] ||
     hyp representation_theorem <> [] ||
     hyp accept_theorem <> [] ||
     not (aconv (concl representation_theorem) expected_representation) ||
     not (aconv (concl accept_theorem) expected_acceptance) then
    failwith "fixed outer postcompute named prover: theorem mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-handoff-end";
  {variable_postcompute_named_raw_result =
     {variable_raw_prepared_source = prepared;
      variable_raw_encoded_jobs_term = named_jobs;
      variable_raw_decoded_jobs_term = decoded_jobs;
      variable_raw_representation_theorem = representation_theorem;
      variable_raw_accept_theorem = accept_theorem};
   variable_postcompute_named_compute_encoded_jobs_term = encoded_jobs;
   variable_postcompute_named_jobs_definition = jobs_definition};;

let candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_prove_encoded_six
    prepared requested_named_jobs encoded_jobs =
  let concrete_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-batch-compute-end";
  candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_handoff_computed_six
    prepared requested_named_jobs encoded_jobs concrete_compute;;

let candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_prove_six
    prepared requested_named_jobs cells =
  if cells = [] then
    failwith "fixed outer postcompute named prover: empty batch";
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-certificate-encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event
    "variable-postcompute-named-certificate-encoding-end";
  candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_prove_encoded_six
    prepared requested_named_jobs encoded_jobs;;

end;;
