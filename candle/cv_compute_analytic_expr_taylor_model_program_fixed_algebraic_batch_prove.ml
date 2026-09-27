(* ========================================================================== *)
(* Proof-producing adapter for one-verdict tagged algebraic Taylor batches.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;

type candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six = {
  fixed_algebraic_batch_center_variant :
    candle_q_dim_taylor_model_program_variant_six;
  fixed_algebraic_batch_lower : term list;
  fixed_algebraic_batch_upper : term list;
};;

type candle_q_dim_taylor_model_fixed_algebraic_batch_result_six = {
  fixed_algebraic_batch_box_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  fixed_algebraic_batch_jobs_term : term;
  fixed_algebraic_batch_encoded_jobs_term : term;
  fixed_algebraic_batch_accept_theorem : thm;
  fixed_algebraic_batch_cells :
    (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six * term * term)
      list;
};;

let candle_q_dim_taylor_model_fixed_algebraic_batch_cval_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_q_dim_taylor_model_fixed_algebraic_batch_cval_list items =
  itlist candle_q_dim_taylor_model_fixed_algebraic_batch_cval_pair
    items `Cexp_num 0`;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_cell_prepare_six cell =
  if length cell.fixed_algebraic_batch_lower <> 6 ||
     length cell.fixed_algebraic_batch_upper <> 6 then
    failwith "fixed algebraic Taylor batch prover: expected six coordinates";
  let boxes =
    candle_poly_fixture_q_boxes
      cell.fixed_algebraic_batch_lower
      cell.fixed_algebraic_batch_upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let job =
    mk_pair
      (cell.fixed_algebraic_batch_center_variant.variant_expression_term,
       boxes) in
  let encoded_job =
    candle_q_dim_taylor_model_fixed_algebraic_batch_cval_pair
      cell.fixed_algebraic_batch_center_variant.
        variant_program_representation_term
      (rand (concl boxes_representation)) in
  cell,job,encoded_job,boxes_representation;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
    box_prepared cells =
  if cells = [] then
    failwith "fixed algebraic Taylor batch prover: empty batch";
  if not
      (List.for_all
        (fun cell ->
          aconv
            cell.fixed_algebraic_batch_center_variant.variant_function_term
            box_prepared.function_term)
        cells) then
    failwith "fixed algebraic Taylor batch prover: source-function mismatch";
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-preparation-begin";
  let prepared =
    map
      candle_q_dim_taylor_model_fixed_algebraic_batch_cell_prepare_six
      cells in
  let jobs =
    mk_list
      (map (fun (_,job,_,_) -> job) prepared,
       type_of (let _,job,_,_ = hd prepared in job)) in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_algebraic_batch_cval_list
      (map (fun (_,_,encoded,_) -> encoded) prepared) in
  let encoding_rewrites =
    candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs_def ::
    List.flatten
      (map
        (fun (cell,_,_,boxes_representation) ->
          [cell.fixed_algebraic_batch_center_variant.variant_compile_theorem;
           cell.fixed_algebraic_batch_center_variant.
             variant_program_representation;
           boxes_representation])
        prepared) in
  let jobs_encoding =
    REWRITE_CONV encoding_rewrites
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs`,jobs)) in
  if hyp jobs_encoding <> [] ||
     not (aconv (rand (concl jobs_encoding)) encoded_jobs) then
    failwith "fixed algebraic Taylor batch prover: job encoding mismatch";
  let box_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        box_prepared.compile_theorem)
      box_prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fsa_batch_check`,
       [box_prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsa_batch_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "fixed algebraic Taylor batch prover: numerical batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-handoff-begin";
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-call-encoding-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fsa_batch_check`)
      [box_program_encoding;jobs_encoding] in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-call-encoding-end";
  let abstract_compute = TRANS call_encoding concrete_compute in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-abstract-compute-linked";
  let correctness =
    SPECL
      [jobs;box_prepared.expression_term]
      candle_cv_fsa_batch_check_correct in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-correctness-instantiated";
  if not
      (aconv (lhand (concl abstract_compute))
             (lhand (concl correctness))) then
    failwith "fixed algebraic Taylor batch prover: abstract checker mismatch";
  let acceptance_encoding = TRANS (SYM abstract_compute) correctness in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-acceptance-encoding-linked";
  let correctness_flag = rand (concl correctness) in
  let flag_operator,flag_body = dest_comb correctness_flag in
  if not (aconv flag_operator `Cexp_num`) then
    failwith
      "fixed algebraic Taylor batch prover: malformed correctness flag";
  let numerical_goal,_ = dest_cond flag_body in
  let flag_theorem =
    let th =
      REWRITE_RULE[injectivity "cval"; SYM ONE] acceptance_encoding in
    let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl th) expected then th
    else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then
      SYM th
    else failwith "fixed algebraic Taylor batch prover: flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-numerical-acceptance-derived";
  let erasure_equalities =
    map
      (fun cell ->
        candle_q_dim_analytic_jet_profile_event
          "fixed-algebraic-certified-taylor-batch-cell-erasure-begin";
        let center =
          mk_comb
            (`candle_analytic_erase_sqrt_certificates`,
             cell.fixed_algebraic_batch_center_variant.
               variant_expression_term) and
            box =
              mk_comb
                (`candle_analytic_erase_sqrt_certificates`,
                 box_prepared.expression_term) in
        let result =
          REWRITE_CONV
            [candle_analytic_erase_sqrt_certificates_def]
            (mk_eq (center,box)) in
        if hyp result <> [] || rand (concl result) <> `T` then
          failwith
            "fixed algebraic Taylor batch prover: erased source mismatch";
        let equality = EQT_ELIM result in
        candle_q_dim_analytic_jet_profile_event
          "fixed-algebraic-certified-taylor-batch-cell-erasure-end";
        equality)
      cells in
  let erasure_goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_algebraic_batch_erasure`,
       [box_prepared.expression_term;jobs]) in
  let erasure_theorem =
    EQT_ELIM
      (REWRITE_CONV
        (candle_q_dim_taylor_model_fixed_algebraic_batch_erasure_def ::
         erasure_equalities)
        erasure_goal) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-erasure-proved";
  let accept_theorem =
    MATCH_MP
      (snd
        (EQ_IMP_RULE
          (SPECL
            [jobs;box_prepared.expression_term]
            candle_q_dim_taylor_model_fixed_algebraic_batch_accept_iff)))
      (CONJ numerical_theorem erasure_theorem) in
  if hyp accept_theorem <> [] then
    failwith "fixed algebraic Taylor batch prover: acceptance assumptions";
  candle_q_dim_analytic_jet_profile_event
    "fixed-algebraic-certified-taylor-batch-handoff-end";
  {
    fixed_algebraic_batch_box_prepared = box_prepared;
    fixed_algebraic_batch_jobs_term = jobs;
    fixed_algebraic_batch_encoded_jobs_term = encoded_jobs;
    fixed_algebraic_batch_accept_theorem = accept_theorem;
    fixed_algebraic_batch_cells =
      map (fun (cell,job,_,_) -> cell,job,rand job) prepared;
  };;

end;;
