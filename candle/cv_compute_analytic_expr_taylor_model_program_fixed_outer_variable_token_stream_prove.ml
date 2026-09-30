(* ========================================================================== *)
(* Proof-producing adapter for raw jobs plus a compact postorder token stream. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_compact_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_compact_sound;;

type candle_q_dim_taylor_model_fixed_outer_variable_token_result_six = {
  variable_token_raw_result :
    candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six;
  variable_token_stream_term : term;
  variable_token_tree_term : term;
  variable_token_run_theorem : thm;
  variable_token_topology_theorem : thm;
  variable_token_source_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_token_source_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens =
  let jobs = raw_result.variable_raw_decoded_jobs_term in
  let run_call =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_token_run`,
       [tokens;jobs;
        `[]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]) in
  candle_q_dim_analytic_jet_profile_event
    "variable-token-stream-reduction-begin";
  let run_theorem =
    REWRITE_CONV
      [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def;
       candle_cv_fso_variable_jobs_decode_def;
       candle_cv_fso_variable_job_decode_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      run_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-token-stream-reduction-end";
  let success,payload = dest_pair (rand (concl run_theorem)) in
  let remaining,stack = dest_pair payload in
  let remaining_items = dest_list remaining in
  if not (aconv success `T`) || remaining_items <> [] then
    failwith
      ("fixed outer variable token prover: stream rejected: success=" ^
       string_of_term success ^ " remaining=" ^ string_of_term remaining);
  let tree =
    match dest_list stack with
    | [tree] -> tree
    | _ -> failwith "fixed outer variable token prover: non-singleton forest" in
  let conservation =
    MATCH_MP
      (SPECL
        [tokens;jobs;
         `[]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`;
         `[]:((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list#
            (((num#num)#num)#((num#num)#num))list))list`;
         stack]
        candle_q_dim_taylor_model_fixed_outer_variable_token_run_jobs)
      run_theorem in
  let tree_jobs =
    REWRITE_RULE
      [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
       APPEND;APPEND_NIL]
      conservation in
  let tree_accept =
    REWRITE_RULE [GSYM tree_jobs]
      raw_result.variable_raw_accept_theorem in
  let prepared = raw_result.variable_raw_prepared_source in
  let projected =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_tree_project`,
       [prepared.expression_term;tree]) in
  let topology =
    mk_comb (`candle_cv_q_dim_taylor_model_tree_topology`,projected) in
  let topology_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_tree_topology_check`,
       [`Cexp_num 6`;topology]) in
  let topology_representation =
    REWRITE_CONV
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_project_def;
       candle_cv_q_dim_taylor_model_tree_topology_def;
       candle_cv_q_interval_list_decode_def;
       candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
       candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
       candle_cv_q_interval_list_def;candle_cv_q_interval_def;
       candle_cv_q_def;candle_cv_lc_z_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      topology_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-token-topology-compute-begin";
  let topology_verdict =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_q_dim_taylor_model_tree_compact_compute_eqs)
      (rand (concl topology_representation)) in
  let topology_theorem =
    TRANS topology_representation topology_verdict in
  candle_q_dim_analytic_jet_profile_event
    "variable-token-topology-compute-end";
  if hyp topology_theorem <> [] ||
     not (aconv (rand (concl topology_theorem)) `Cexp_num 1`) then
    failwith "fixed outer variable token prover: topology rejected";
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`;tree]
        candle_cv_q_dim_taylor_model_fixed_outer_variable_tree_compact_sound) in
  let premise =
    CONJ prepared.valid_theorem (CONJ tree_accept topology_theorem) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer variable token prover: soundness premise mismatch";
  let cell_theorem = MATCH_MP soundness premise in
  let source_theorem =
    REWRITE_RULE
      [m_cell_pass;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def;
       prepared.source_theorem]
      cell_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed outer variable token prover: source assumptions";
  {variable_token_raw_result = raw_result;
   variable_token_stream_term = tokens;
   variable_token_tree_term = tree;
   variable_token_run_theorem = run_theorem;
   variable_token_topology_theorem = topology_theorem;
   variable_token_source_theorem = source_theorem};;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_TOKEN_STREAM_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
