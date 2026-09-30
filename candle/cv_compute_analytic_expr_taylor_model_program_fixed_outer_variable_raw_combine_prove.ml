(* ========================================================================== *)
(* Balanced logical composition of independently checked raw job batches.    *)
(*                                                                            *)
(* Numerical batches remain bounded.  Composition uses the proved APPEND     *)
(* law for logical job acceptance and does not re-run or trust computation.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_combine_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove;;

type candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_six = {
  variable_raw_acceptance_prepared : candle_q_dim_analytic_jet_prepared_six;
  variable_raw_acceptance_jobs_term : term;
  variable_raw_acceptance_theorem : thm;
  variable_raw_acceptance_compute_count : int;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_validate
    prepared jobs theorem =
  let expected =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;jobs]) in
  if hyp theorem <> [] || not (aconv (concl theorem) expected) then
    failwith "fixed outer variable raw combine: acceptance mismatch";;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_of_result
    (result:candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six) =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_validate
    result.variable_raw_prepared_source
    result.variable_raw_decoded_jobs_term
    result.variable_raw_accept_theorem;
  {variable_raw_acceptance_prepared = result.variable_raw_prepared_source;
   variable_raw_acceptance_jobs_term = result.variable_raw_decoded_jobs_term;
   variable_raw_acceptance_theorem = result.variable_raw_accept_theorem;
   variable_raw_acceptance_compute_count = 1};;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_merge
    left right =
  let prepared = left.variable_raw_acceptance_prepared in
  if not
       (aconv prepared.expression_term
         right.variable_raw_acceptance_prepared.expression_term) then
    failwith "fixed outer variable raw combine: source mismatch";
  let left_jobs = left.variable_raw_acceptance_jobs_term
  and right_jobs = right.variable_raw_acceptance_jobs_term in
  let jobs = mk_icomb (mk_icomb (`APPEND`,left_jobs),right_jobs) in
  let theorem =
    EQ_MP
      (SYM
        (SPECL
          [left_jobs;right_jobs;prepared.expression_term]
          candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_append))
      (CONJ left.variable_raw_acceptance_theorem
        right.variable_raw_acceptance_theorem) in
  candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_validate
    prepared jobs theorem;
  {variable_raw_acceptance_prepared = prepared;
   variable_raw_acceptance_jobs_term = jobs;
   variable_raw_acceptance_theorem = theorem;
   variable_raw_acceptance_compute_count =
     left.variable_raw_acceptance_compute_count +
     right.variable_raw_acceptance_compute_count};;

let rec candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_level =
  function
  | [] -> []
  | [single] -> [single]
  | left :: right :: remaining ->
      candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_merge
        left right ::
      candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_level
        remaining;;

let rec candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_collapse =
  function
  | [] -> failwith "fixed outer variable raw combine: empty batch list"
  | [single] -> single
  | batches ->
      candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_collapse
        (candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_level
          batches);;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_combine
    results =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_collapse
    (map
      candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_of_result
      results);;

let candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_source_six
    acceptance tokens =
  candle_q_dim_taylor_model_fixed_outer_variable_token_acceptance_six
    acceptance.variable_raw_acceptance_prepared
    acceptance.variable_raw_acceptance_jobs_term
    acceptance.variable_raw_acceptance_theorem tokens;;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_RAW_COMBINE_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
