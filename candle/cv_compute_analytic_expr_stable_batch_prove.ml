(* ========================================================================== *)
(* Proof-producing adapter for stable-source fixed-algebraic Taylor batches. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The analytic source and its compiled program  *)
(* are authenticated once.  Whole-box and center square-root certificates    *)
(* remain ordinary data checked by one reflected call.  The general stable   *)
(* batch handoff then reuses the established certified Taylor soundness.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

module Candle_cv_analytic_expr_stable_batch_prove = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;

type candle_q_dim_taylor_model_stable_batch_cell_six = {
  stable_batch_center_intervals : term list;
  stable_batch_lower : term list;
  stable_batch_upper : term list;
};;

type candle_q_dim_taylor_model_stable_batch_prepared_cell_six = {
  stable_batch_cell : candle_q_dim_taylor_model_stable_batch_cell_six;
  stable_batch_center_intervals_term : term;
  stable_batch_boxes_term : term;
  stable_batch_job_term : term;
  stable_batch_materialized_job_term : term;
  stable_batch_encoded_job_term : term;
  stable_batch_center_intervals_representation : thm;
  stable_batch_boxes_representation : thm;
};;

type candle_q_dim_taylor_model_stable_batch_result_six = {
  stable_batch_prepared_source : candle_q_dim_analytic_jet_prepared_six;
  stable_batch_box_intervals_term : term;
  stable_batch_jobs_term : term;
  stable_batch_materialized_jobs_term : term;
  stable_batch_accept_theorem : thm;
  stable_batch_prepared_cells :
    candle_q_dim_taylor_model_stable_batch_prepared_cell_six list;
};;

let candle_q_dim_taylor_model_stable_batch_interval_type =
 `:((num#num)#num)#((num#num)#num)`;;

let candle_q_dim_taylor_model_stable_batch_cval_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_q_dim_taylor_model_stable_batch_cval_list items =
  itlist candle_q_dim_taylor_model_stable_batch_cval_pair
    items `Cexp_num 0`;;

let candle_q_dim_taylor_model_stable_batch_patch_expression
    intervals source_e =
  let patched =
    list_mk_comb
      (`candle_analytic_patch_sqrt_certificates`,[intervals;source_e]) in
  mk_icomb (`SND`,patched);;

let candle_q_dim_taylor_model_stable_batch_prepare_cell_six
    source_e cell =
  if length cell.stable_batch_lower <> 6 ||
     length cell.stable_batch_upper <> 6 then
    failwith "stable Taylor batch prover: expected six coordinates";
  let center_intervals =
    mk_list
      (cell.stable_batch_center_intervals,
       candle_q_dim_taylor_model_stable_batch_interval_type) in
  let boxes =
    candle_poly_fixture_q_boxes
      cell.stable_batch_lower cell.stable_batch_upper in
  let center_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv center_intervals and
      boxes_representation =
        candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let job = mk_pair (center_intervals,boxes) in
  let materialized_job =
    mk_pair
      (candle_q_dim_taylor_model_stable_batch_patch_expression
        center_intervals source_e,
       boxes) in
  let encoded_job =
    candle_q_dim_taylor_model_stable_batch_cval_pair
      (rand (concl center_representation))
      (rand (concl boxes_representation)) in
  {stable_batch_cell = cell;
   stable_batch_center_intervals_term = center_intervals;
   stable_batch_boxes_term = boxes;
   stable_batch_job_term = job;
   stable_batch_materialized_job_term = materialized_job;
   stable_batch_encoded_job_term = encoded_job;
   stable_batch_center_intervals_representation = center_representation;
   stable_batch_boxes_representation = boxes_representation};;

let candle_q_dim_taylor_model_stable_batch_prove_six
    prepared box_intervals cells =
  if cells = [] then failwith "stable Taylor batch prover: empty batch";
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
    failwith "stable Taylor batch prover: job encoding mismatch";
  let box_intervals_encoding =
    candle_q_dim_analytic_jet_boxes_encode_conv box_intervals_term in
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fsa_stable_batch_check`,
       [prepared.program_representation_term;
        rand (concl box_intervals_encoding);encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsa_stable_batch_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "stable Taylor batch prover: numerical batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fsa_stable_batch_check`)
      [source_program_encoding;box_intervals_encoding;jobs_encoding] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let correctness =
    SPECL
      [prepared.expression_term;box_intervals_term;jobs]
      candle_cv_fsa_stable_batch_check_correct in
  if not
      (aconv (lhand (concl abstract_compute))
             (lhand (concl correctness))) then
    failwith "stable Taylor batch prover: abstract checker mismatch";
  let acceptance_encoding = TRANS (SYM abstract_compute) correctness in
  let correctness_flag = rand (concl correctness) in
  let flag_operator,flag_body = dest_comb correctness_flag in
  if not (aconv flag_operator `Cexp_num`) then
    failwith "stable Taylor batch prover: malformed correctness flag";
  let numerical_goal,_ = dest_cond flag_body in
  let flag_theorem =
    let theorem =
      REWRITE_RULE[injectivity "cval"; SYM ONE] acceptance_encoding in
    let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl theorem) expected then theorem
    else if aconv (concl theorem) (mk_eq (rand expected,lhand expected)) then
      SYM theorem
    else failwith "stable Taylor batch prover: flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [prepared.expression_term;box_intervals_term;jobs]
        candle_q_dim_taylor_model_stable_batch_accept)
      numerical_theorem in
  if hyp accept_theorem <> [] then
    failwith "stable Taylor batch prover: acceptance assumptions";
  candle_q_dim_analytic_jet_profile_event
    "stable-certified-taylor-batch-handoff-end";
  {stable_batch_prepared_source = prepared;
   stable_batch_box_intervals_term = box_intervals_term;
   stable_batch_jobs_term = jobs;
   stable_batch_materialized_jobs_term = materialized_jobs;
   stable_batch_accept_theorem = accept_theorem;
   stable_batch_prepared_cells = prepared_cells};;

let candle_q_dim_taylor_model_stable_batch_cell_accept_six result cell =
  let prepared_cell =
    try
      find
        (fun candidate ->
          candidate.stable_batch_cell.stable_batch_lower =
            cell.stable_batch_lower &&
          candidate.stable_batch_cell.stable_batch_upper =
            cell.stable_batch_upper &&
          candidate.stable_batch_cell.stable_batch_center_intervals =
            cell.stable_batch_center_intervals)
        result.stable_batch_prepared_cells
    with Not_found -> failwith "stable Taylor batch prover: unknown cell" in
  let membership =
    EQT_ELIM
      (REWRITE_CONV
        [candle_q_dim_taylor_model_stable_jobs_materialize_def; MEM;
         FST; SND]
        (list_mk_comb
          (`MEM:(candle_analytic_expr#
                 (((num#num)#num)#((num#num)#num))list)->
                (candle_analytic_expr#
                 (((num#num)#num)#((num#num)#num))list)list->bool`,
           [prepared_cell.stable_batch_materialized_job_term;
            result.stable_batch_materialized_jobs_term]))) in
  let implication =
    SPECL
      [result.stable_batch_materialized_jobs_term;
       candle_q_dim_taylor_model_stable_batch_patch_expression
         result.stable_batch_box_intervals_term
         result.stable_batch_prepared_source.expression_term;
       prepared_cell.stable_batch_materialized_job_term]
      candle_q_dim_taylor_model_fixed_algebraic_batch_accept_mem in
  let premise = CONJ result.stable_batch_accept_theorem membership in
  if not (aconv (fst (dest_imp (concl implication))) (concl premise)) then
    failwith "stable Taylor batch prover: cell premise mismatch";
  REWRITE_RULE[FST;SND] (MATCH_MP implication premise);;

let candle_q_dim_taylor_model_stable_batch_sound_six =
  REWRITE_RULE
    [candle_q_dim_analytic_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_taylor_model_fixed_algebraic_certified_accept_sound);;

let candle_q_dim_taylor_model_stable_batch_cell_source_six result cell =
  let acceptance =
    candle_q_dim_taylor_model_stable_batch_cell_accept_six result cell in
  let prepared_cell =
    find
      (fun candidate ->
        candidate.stable_batch_cell.stable_batch_lower =
          cell.stable_batch_lower &&
        candidate.stable_batch_cell.stable_batch_upper =
          cell.stable_batch_upper &&
        candidate.stable_batch_cell.stable_batch_center_intervals =
          cell.stable_batch_center_intervals)
      result.stable_batch_prepared_cells in
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
        candle_q_dim_taylor_model_stable_batch_sound_six)
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
    failwith "stable Taylor batch prover: source theorem assumptions";
  source_theorem;;

end;;
