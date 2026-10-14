(* ========================================================================== *)
(* Genuine case-10173: compose exact registered checked-result chunks.       *)
(*                                                                            *)
(* The HOL4 registration ledger returns a balanced tree of ordinary Candle   *)
(* equalities.  This layer splits that tree, turns each checked raw result    *)
(* (plus its independently checked structural guard) into source-level cell  *)
(* facts, and combines the facts without reconstructing arithmetic theorems. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_batch_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_registered_combine = struct

open Candle_cv_analytic_expr_case10173_historical_source_contract;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_batch_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

(* Keep the data-list append lemma local to the historical checker.  This
   avoids pulling the older fixed-nonlinear proof constructor into the fast
   registered path merely for its identical encoded-list operation. *)

let candle_cv_case10173_hist_encoded_jobs_append_def = define
 `(candle_cv_case10173_hist_encoded_jobs_append (Cexp_num n) right = right) /\
  (candle_cv_case10173_hist_encoded_jobs_append
      (Cexp_pair job jobs) right =
     Cexp_pair job
       (candle_cv_case10173_hist_encoded_jobs_append jobs right))`;;

let candle_cv_case10173_hist_jobs_encode_append = prove
 (`!left right.
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (APPEND left right) =
     candle_cv_case10173_hist_encoded_jobs_append
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs left)
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs right)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [APPEND;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_case10173_hist_encoded_jobs_append_def]);;

type candle_case10173_hist_registered_acceptance = {
  registered_acceptance_encoded_jobs : term;
  registered_acceptance_decoded_jobs : term;
  registered_acceptance_representation : thm;
  registered_acceptance_jobs_pass : thm;
  registered_acceptance_chunk_count : int;
};;

let candle_case10173_hist_registered_source_program =
  `candle_cv_analytic_instruction_list
     (candle_analytic_compile candle_case10173_hist_authenticated_source)`;;

let candle_case10173_hist_registered_validate
    encoded decoded representation jobs_pass =
  let expected_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,decoded),
       encoded) in
  let expected_jobs_pass =
    list_mk_comb
      (`candle_case10173_hist_jobs_pass`,
       [`candle_case10173_hist_authenticated_source`;decoded]) in
  if hyp representation <> [] ||
     not (aconv (concl representation) expected_representation)
  then failwith "case10173 registered combine: representation mismatch";
  if hyp jobs_pass <> [] || not (aconv (concl jobs_pass) expected_jobs_pass)
  then failwith "case10173 registered combine: jobs-pass mismatch";;

let candle_case10173_hist_registered_acceptance_of_theorems
    encoded roots well_formed checked =
  let expected_well_formed =
    mk_eq
      (mk_comb (`candle_cv_case10173_hist_jobs_well_formed`,encoded),
       `Cexp_num 1`) in
  let expected_checked =
    mk_eq
      (list_mk_comb
        (`candle_cv_case10173_hist_checked_raw_jobs_check`,
         [candle_case10173_hist_registered_source_program;encoded;roots]),
       `Cexp_num 1`) in
  if hyp well_formed <> [] ||
     not (aconv (concl well_formed) expected_well_formed)
  then failwith "case10173 registered combine: well-formedness mismatch";
  if hyp checked <> [] || not (aconv (concl checked) expected_checked)
  then failwith "case10173 registered combine: checked-result mismatch";
  let decoded =
    mk_comb (`candle_cv_fso_variable_jobs_decode`,encoded) in
  let accepted =
    MATCH_MP
      (SPECL
        [candle_case10173_hist_registered_source_program;encoded;roots]
        candle_cv_case10173_hist_checked_raw_jobs_accept)
      checked in
  let representation = CONJUNCT1 accepted in
  let jobs_pass =
    MATCH_MP
      (SPECL
        [encoded;roots]
        candle_case10173_hist_authenticated_checked_raw_jobs_sound)
      (CONJ well_formed checked) in
  candle_case10173_hist_registered_validate
    encoded decoded representation jobs_pass;
  {registered_acceptance_encoded_jobs = encoded;
   registered_acceptance_decoded_jobs = decoded;
   registered_acceptance_representation = representation;
   registered_acceptance_jobs_pass = jobs_pass;
   registered_acceptance_chunk_count = 1};;

let candle_case10173_hist_registered_acceptance_merge left right =
  let left_jobs = left.registered_acceptance_decoded_jobs
  and right_jobs = right.registered_acceptance_decoded_jobs in
  let jobs = mk_icomb (mk_icomb (`APPEND`,left_jobs),right_jobs) in
  let encoded_call =
    list_mk_comb
      (`candle_cv_case10173_hist_encoded_jobs_append`,
       [left.registered_acceptance_encoded_jobs;
        right.registered_acceptance_encoded_jobs]) in
  let encoding =
    REWRITE_CONV [candle_cv_case10173_hist_encoded_jobs_append_def]
      encoded_call in
  let encoded = rand (concl encoding) in
  let representation =
    TRANS
      (REWRITE_RULE
        [left.registered_acceptance_representation;
         right.registered_acceptance_representation]
        (SPECL
          [left_jobs;right_jobs]
          candle_cv_case10173_hist_jobs_encode_append))
      encoding in
  let jobs_pass =
    EQ_MP
      (SYM
        (SPECL
          [left_jobs;right_jobs;
           `candle_case10173_hist_authenticated_source`]
          candle_case10173_hist_jobs_pass_append))
      (CONJ left.registered_acceptance_jobs_pass
        right.registered_acceptance_jobs_pass) in
  candle_case10173_hist_registered_validate
    encoded jobs representation jobs_pass;
  {registered_acceptance_encoded_jobs = encoded;
   registered_acceptance_decoded_jobs = jobs;
   registered_acceptance_representation = representation;
   registered_acceptance_jobs_pass = jobs_pass;
   registered_acceptance_chunk_count =
     left.registered_acceptance_chunk_count +
     right.registered_acceptance_chunk_count};;

let rec candle_case10173_hist_registered_acceptance_level = function
  | [] -> []
  | [single] -> [single]
  | left :: right :: remaining ->
      candle_case10173_hist_registered_acceptance_merge left right ::
      candle_case10173_hist_registered_acceptance_level remaining;;

let rec candle_case10173_hist_registered_acceptance_collapse = function
  | [] -> failwith "case10173 registered combine: empty acceptance list"
  | [single] -> single
  | acceptances ->
      candle_case10173_hist_registered_acceptance_collapse
        (candle_case10173_hist_registered_acceptance_level acceptances);;

(* Splitting by [FST] and [SND] avoids expanding all constructor-injectivity
   rewrites at once.  It therefore follows the same balanced shape as the
   registered ledger and retains one closed equality per numerical chunk. *)

let rec candle_case10173_hist_registered_pair_result_leaves theorem =
  let left,right = dest_eq (concl theorem) in
  let left_operator,left_arguments = strip_comb left
  and right_operator,right_arguments = strip_comb right in
  let left_name,_ = dest_const left_operator
  and right_name,_ = dest_const right_operator in
  match left_name,left_arguments,right_name,right_arguments with
  | "Cexp_pair",[_;_],"Cexp_pair",[_;_] ->
      let first =
        PURE_REWRITE_RULE [cexp_fst_def] (AP_TERM `Cexp_fst` theorem) in
      let second =
        PURE_REWRITE_RULE [cexp_snd_def] (AP_TERM `Cexp_snd` theorem) in
      candle_case10173_hist_registered_pair_result_leaves first @
      candle_case10173_hist_registered_pair_result_leaves second
  | _ -> [theorem];;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_COMBINE_OK DEVELOPMENT_NON_RELEASE";;

end;;
