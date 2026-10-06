(* Balanced logical composition of independently checked fixed-nonlinear raw *)
(* job batches.  Numerical computations remain bounded; the general APPEND   *)
(* theorem combines their closed logical acceptance results.                 *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_append =
  prove
   (`!left right source_e.
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
         source_e (APPEND left right) <=>
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
         source_e left /\
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
         source_e right`,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC
      [APPEND;
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def] THEN
    MESON_TAC[]);;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_six = {
  fixed_nonlinear_raw_acceptance_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  fixed_nonlinear_raw_acceptance_jobs_term : term;
  fixed_nonlinear_raw_acceptance_theorem : thm;
  fixed_nonlinear_raw_acceptance_compute_count : int;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_validate
    prepared jobs theorem =
  let expected =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept`,
       [prepared.expression_term;jobs]) in
  if hyp theorem <> [] || not (aconv (concl theorem) expected) then
    failwith "fixed nonlinear raw combine: acceptance mismatch";;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_of_result
    (result:candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_six) =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_validate
    result.fixed_nonlinear_variable_raw_prepared_source
    result.fixed_nonlinear_variable_raw_decoded_jobs_term
    result.fixed_nonlinear_variable_raw_accept_theorem;
  {fixed_nonlinear_raw_acceptance_prepared =
     result.fixed_nonlinear_variable_raw_prepared_source;
   fixed_nonlinear_raw_acceptance_jobs_term =
     result.fixed_nonlinear_variable_raw_decoded_jobs_term;
   fixed_nonlinear_raw_acceptance_theorem =
     result.fixed_nonlinear_variable_raw_accept_theorem;
   fixed_nonlinear_raw_acceptance_compute_count = 1};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_merge
    left right =
  let prepared = left.fixed_nonlinear_raw_acceptance_prepared in
  if not
       (aconv prepared.expression_term
         right.fixed_nonlinear_raw_acceptance_prepared.expression_term) then
    failwith "fixed nonlinear raw combine: source mismatch";
  let left_jobs = left.fixed_nonlinear_raw_acceptance_jobs_term
  and right_jobs = right.fixed_nonlinear_raw_acceptance_jobs_term in
  let jobs = mk_icomb (mk_icomb (`APPEND`,left_jobs),right_jobs) in
  let theorem =
    EQ_MP
      (SYM
        (SPECL
          [left_jobs;right_jobs;prepared.expression_term]
          candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_append))
      (CONJ left.fixed_nonlinear_raw_acceptance_theorem
        right.fixed_nonlinear_raw_acceptance_theorem) in
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_validate
    prepared jobs theorem;
  {fixed_nonlinear_raw_acceptance_prepared = prepared;
   fixed_nonlinear_raw_acceptance_jobs_term = jobs;
   fixed_nonlinear_raw_acceptance_theorem = theorem;
   fixed_nonlinear_raw_acceptance_compute_count =
     left.fixed_nonlinear_raw_acceptance_compute_count +
     right.fixed_nonlinear_raw_acceptance_compute_count};;

let rec candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_level =
  function
  | [] -> []
  | [single] -> [single]
  | left :: right :: remaining ->
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_merge
        left right ::
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_level
        remaining;;

let rec candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_collapse =
  function
  | [] -> failwith "fixed nonlinear raw combine: empty batch list"
  | [single] -> single
  | batches ->
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_collapse
        (candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_level
          batches);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_combine
    results =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_collapse
    (map
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_of_result
      results);;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_RAW_COMBINE_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
