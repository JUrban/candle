(* ========================================================================== *)
(* Proof-producing adapter for stable-source fixed-outer Taylor batches.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound;;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
    prepared box_intervals cells =
  if cells = [] then
    failwith "fixed outer stable Taylor batch prover: empty batch";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-preparation-begin";
  let box_intervals_term =
    mk_list
      (box_intervals,
       candle_q_dim_taylor_model_stable_batch_interval_type) in
  let prepared_cells =
    map
      (candle_q_dim_taylor_model_stable_batch_prepare_cell_six
        prepared.expression_term)
      cells in
  let jobs =
    mk_list
      (map (fun cell -> cell.stable_batch_job_term) prepared_cells,
       type_of (hd prepared_cells).stable_batch_job_term) in
  let materialized_jobs =
    list_mk_comb
      (`candle_q_dim_taylor_model_stable_jobs_materialize`,
       [prepared.expression_term;jobs]) in
  let encoded_jobs =
    candle_q_dim_taylor_model_stable_batch_cval_list
      (map (fun cell -> cell.stable_batch_encoded_job_term) prepared_cells) in
  let jobs_encoding =
    REWRITE_CONV
      (candle_cv_q_dim_taylor_model_stable_jobs_def ::
       List.flatten
         (map
           (fun cell ->
             [cell.stable_batch_center_intervals_representation;
              cell.stable_batch_boxes_representation])
           prepared_cells))
      (mk_comb (`candle_cv_q_dim_taylor_model_stable_jobs`,jobs)) in
  if hyp jobs_encoding <> [] ||
     not (aconv (rand (concl jobs_encoding)) encoded_jobs) then
    failwith "fixed outer stable Taylor batch prover: job encoding mismatch";
  let box_intervals_encoding =
    candle_q_dim_analytic_jet_boxes_encode_conv box_intervals_term in
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fso_stable_batch_check`,
       [prepared.program_representation_term;
        rand (concl box_intervals_encoding);encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "fixed outer stable Taylor batch prover: numerical batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fso_stable_batch_check`)
      [source_program_encoding;box_intervals_encoding;jobs_encoding] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let correctness =
    SPECL
      [prepared.expression_term;box_intervals_term;jobs]
      candle_cv_fso_stable_batch_check_correct in
  if not
      (aconv (lhand (concl abstract_compute))
             (lhand (concl correctness))) then
    failwith "fixed outer stable Taylor batch prover: abstract checker mismatch";
  let acceptance_encoding = TRANS (SYM abstract_compute) correctness in
  let correctness_flag = rand (concl correctness) in
  let flag_operator,flag_body = dest_comb correctness_flag in
  if not (aconv flag_operator `Cexp_num`) then
    failwith "fixed outer stable Taylor batch prover: malformed flag";
  let numerical_goal,_ = dest_cond flag_body in
  let flag_theorem =
    let theorem =
      REWRITE_RULE[injectivity "cval"; SYM ONE] acceptance_encoding in
    let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl theorem) expected then theorem
    else if aconv (concl theorem) (mk_eq (rand expected,lhand expected)) then
      SYM theorem
    else failwith "fixed outer stable Taylor batch prover: flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [prepared.expression_term;box_intervals_term;jobs]
        candle_q_dim_taylor_model_fixed_outer_stable_batch_accept)
      numerical_theorem in
  if hyp accept_theorem <> [] then
    failwith "fixed outer stable Taylor batch prover: acceptance assumptions";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-handoff-end";
  {stable_batch_prepared_source = prepared;
   stable_batch_box_intervals_term = box_intervals_term;
   stable_batch_jobs_term = jobs;
   stable_batch_materialized_jobs_term = materialized_jobs;
   stable_batch_accept_theorem = accept_theorem;
   stable_batch_prepared_cells = prepared_cells};;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_accepts_six
    result =
  let rec extract accepted prepared_cells =
    match prepared_cells with
    | [] -> []
    | prepared_cell :: remaining ->
        let materialized_head =
          CONV_RULE
            (RAND_CONV
              (REWR_CONV
                (CONJUNCT2
                  candle_q_dim_taylor_model_stable_jobs_materialize_def)))
            accepted in
        let split =
          CONV_RULE
            (REWR_CONV
              (CONJUNCT2
                candle_q_dim_taylor_model_fixed_outer_batch_accept_def))
            materialized_head in
        let cell_acceptance =
          REWRITE_RULE[FST;SND] (CONJUNCT1 split) in
        (prepared_cell,cell_acceptance) ::
        extract (CONJUNCT2 split) remaining in
  extract result.stable_batch_accept_theorem
    result.stable_batch_prepared_cells;;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_accept_six
    result cell =
  try
    snd
      (find
        (fun (prepared_cell,_) ->
          candle_q_dim_taylor_model_stable_batch_cell_matches
            prepared_cell.stable_batch_cell cell)
        (candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_accepts_six
          result))
  with Not_found ->
    failwith "fixed outer stable Taylor batch prover: unknown cell";;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_sound_six =
  REWRITE_RULE
    [candle_q_dim_analytic_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_taylor_model_fixed_outer_certified_accept_sound);;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_prepared_cell_source_six
    result prepared_cell acceptance =
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
           prepared_cell.stable_batch_boxes_term),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let box_expression =
    candle_q_dim_taylor_model_stable_batch_patch_expression
      result.stable_batch_box_intervals_term
      result.stable_batch_prepared_source.expression_term in
  let valid =
    MATCH_MP
      (SPECL
        [result.stable_batch_prepared_source.expression_term;
         result.stable_batch_box_intervals_term;`6`]
        candle_analytic_patch_sqrt_certificates_valid_dim)
      result.stable_batch_prepared_source.valid_theorem in
  let vector_theorem =
    MATCH_MP
      (SPECL
        [candle_q_dim_taylor_model_stable_batch_patch_expression
           prepared_cell.stable_batch_center_intervals_term
           result.stable_batch_prepared_source.expression_term;
         box_expression;prepared_cell.stable_batch_boxes_term]
        candle_q_dim_taylor_model_fixed_outer_stable_batch_sound_six)
      (CONJ valid (CONJ length_six acceptance)) in
  let denotation =
    INST_TYPE
      [`:6`,`:N`]
      (SPECL
        [result.stable_batch_prepared_source.expression_term;
         result.stable_batch_box_intervals_term]
        candle_analytic_patch_sqrt_certificates_denote_dim) in
  let source_theorem =
    REWRITE_RULE
      [SYM denotation;
       result.stable_batch_prepared_source.source_theorem]
      vector_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed outer stable Taylor batch prover: source assumptions";
  source_theorem;;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_sources_six
    result =
  map
    (fun (prepared_cell,acceptance) ->
      candle_q_dim_taylor_model_fixed_outer_stable_batch_prepared_cell_source_six
        result prepared_cell acceptance)
    (candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_accepts_six
      result);;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_source_six
    result cell =
  try
    let prepared_cell,acceptance =
      find
        (fun (prepared_cell,_) ->
          candle_q_dim_taylor_model_stable_batch_cell_matches
            prepared_cell.stable_batch_cell cell)
        (candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_accepts_six
          result) in
    candle_q_dim_taylor_model_fixed_outer_stable_batch_prepared_cell_source_six
      result prepared_cell acceptance
  with Not_found ->
    failwith "fixed outer stable Taylor batch prover: unknown cell";;

end;;
