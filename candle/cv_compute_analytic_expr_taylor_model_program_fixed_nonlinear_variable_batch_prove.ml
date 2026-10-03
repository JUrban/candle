(* ========================================================================== *)
(* Proof-producing adapter for per-job fixed-nonlinear certificate batches.  *)
(*                                                                            *)
(* The source expression and compiled skeleton are authenticated once.  Each  *)
(* job carries whole-box and center square-root certificates plus its box as  *)
(* checked data.  One reflected verdict yields the per-cell source theorems.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_result_six = {
  fixed_nonlinear_variable_batch_prepared_source :
    candle_q_dim_analytic_jet_prepared_six;
  fixed_nonlinear_variable_batch_jobs_term : term;
  fixed_nonlinear_variable_batch_accept_theorem : thm;
  fixed_nonlinear_variable_batch_prepared_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_prepared_cell_six list;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_prove_six
    prepared cells =
  if cells = [] then
    failwith "fixed nonlinear variable batch prover: empty batch";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-preparation-begin";
  let prepared_cells =
    map
      (candle_q_dim_taylor_model_fixed_outer_variable_batch_prepare_cell_six
        prepared.expression_term)
      cells in
  let jobs =
    mk_list
      (map (fun cell -> cell.variable_batch_job_term) prepared_cells,
       type_of (hd prepared_cells).variable_batch_job_term) in
  let encoded_jobs =
    candle_q_dim_taylor_model_stable_batch_cval_list
      (map
        (fun cell -> cell.variable_batch_encoded_job_term)
        prepared_cells) in
  let jobs_encoding =
    REWRITE_CONV
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def ::
       List.flatten
         (map
           (fun cell ->
             [cell.variable_batch_box_intervals_representation;
              cell.variable_batch_stable_prepared_cell.
                stable_batch_center_intervals_representation;
              cell.variable_batch_stable_prepared_cell.
                stable_batch_boxes_representation])
           prepared_cells))
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,jobs)) in
  if hyp jobs_encoding <> [] ||
     not (aconv (rand (concl jobs_encoding)) encoded_jobs) then
    failwith "fixed nonlinear variable batch prover: job encoding mismatch";
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fsn_variable_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fixed_nonlinear_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "fixed nonlinear variable batch prover: numerical batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fsn_variable_jobs_check`)
      [source_program_encoding;jobs_encoding] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let correctness =
    SPECL
      [jobs;prepared.expression_term]
      candle_cv_fsn_variable_jobs_check_correct in
  if not
      (aconv (lhand (concl abstract_compute))
             (lhand (concl correctness))) then
    failwith "fixed nonlinear variable batch prover: abstract checker mismatch";
  let acceptance_encoding = TRANS (SYM abstract_compute) correctness in
  let correctness_flag = rand (concl correctness) in
  let flag_operator,flag_body = dest_comb correctness_flag in
  if not (aconv flag_operator `Cexp_num`) then
    failwith "fixed nonlinear variable batch prover: malformed flag";
  let numerical_goal,_ = dest_cond flag_body in
  let flag_theorem =
    let theorem =
      REWRITE_RULE[injectivity "cval"; SYM ONE] acceptance_encoding in
    let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl theorem) expected then theorem
    else if aconv (concl theorem) (mk_eq (rand expected,lhand expected)) then
      SYM theorem
    else failwith "fixed nonlinear variable batch prover: flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [jobs;prepared.expression_term]
        candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept)
      numerical_theorem in
  if hyp accept_theorem <> [] then
    failwith "fixed nonlinear variable batch prover: acceptance assumptions";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-batch-handoff-end";
  {fixed_nonlinear_variable_batch_prepared_source = prepared;
   fixed_nonlinear_variable_batch_jobs_term = jobs;
   fixed_nonlinear_variable_batch_accept_theorem = accept_theorem;
   fixed_nonlinear_variable_batch_prepared_cells = prepared_cells};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_cell_accepts_six
    result =
  let rec extract accepted prepared_cells =
    match prepared_cells with
    | [] -> []
    | prepared_cell :: remaining ->
        let split =
          CONV_RULE
            (REWR_CONV
              (CONJUNCT2
                candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def))
            accepted in
        (prepared_cell,REWRITE_RULE[FST;SND] (CONJUNCT1 split)) ::
        extract (CONJUNCT2 split) remaining in
  extract result.fixed_nonlinear_variable_batch_accept_theorem
    result.fixed_nonlinear_variable_batch_prepared_cells;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_sound_six =
  REWRITE_RULE
    [candle_q_dim_analytic_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_sound);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_cell_source_six
    result prepared_cell acceptance =
  let stable = prepared_cell.variable_batch_stable_prepared_cell in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
           stable.stable_batch_boxes_term),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let source_e =
    result.fixed_nonlinear_variable_batch_prepared_source.expression_term in
  let box_expression =
    candle_q_dim_taylor_model_stable_batch_patch_expression
      prepared_cell.variable_batch_box_intervals_term source_e in
  let center_expression =
    candle_q_dim_taylor_model_stable_batch_patch_expression
      stable.stable_batch_center_intervals_term source_e in
  let valid =
    MATCH_MP
      (SPECL
        [source_e;prepared_cell.variable_batch_box_intervals_term;`6`]
        candle_analytic_patch_sqrt_certificates_valid_dim)
      result.fixed_nonlinear_variable_batch_prepared_source.valid_theorem in
  let vector_theorem =
    MATCH_MP
      (SPECL
        [center_expression;box_expression;stable.stable_batch_boxes_term]
        candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_sound_six)
      (CONJ valid (CONJ length_six acceptance)) in
  let denotation =
    INST_TYPE
      [`:6`,`:N`]
      (SPECL
        [source_e;prepared_cell.variable_batch_box_intervals_term]
        candle_analytic_patch_sqrt_certificates_denote_dim) in
  let source_theorem =
    REWRITE_RULE
      [SYM denotation;
       result.fixed_nonlinear_variable_batch_prepared_source.source_theorem]
      vector_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed nonlinear variable batch prover: source assumptions";
  source_theorem;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_sources_six
    result =
  map
    (fun (prepared_cell,acceptance) ->
      candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_cell_source_six
        result prepared_cell acceptance)
    (candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_cell_accepts_six
      result);;

end;;
