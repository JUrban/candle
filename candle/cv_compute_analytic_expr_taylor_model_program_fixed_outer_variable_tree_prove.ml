(* ========================================================================== *)
(* Proof-producing one-root handoff for variable-certificate split trees.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_compact_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_compact_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_source_six
    (result:
      candle_q_dim_taylor_model_fixed_outer_variable_batch_result_six)
    tree =
  let jobs_call =
    mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs`,tree) in
  let jobs_expansion =
    REWRITE_CONV
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;APPEND]
      jobs_call in
  if hyp jobs_expansion <> [] ||
     not
       (aconv (rand (concl jobs_expansion))
         result.variable_batch_jobs_term) then
    failwith "fixed outer variable tree prover: tree/batch job mismatch";
  let tree_accept =
    REWRITE_RULE[SYM jobs_expansion]
      result.variable_batch_accept_theorem in
  let projected =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_tree_project`,
       [result.variable_batch_prepared_source.expression_term;tree]) in
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
       candle_cv_q_interval_list_def; candle_cv_q_interval_def;
       candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
      topology_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-tree-topology-compute-begin";
  let topology_verdict =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_q_dim_taylor_model_tree_compact_compute_eqs)
      (rand (concl topology_representation)) in
  let topology_compute =
    TRANS topology_representation topology_verdict in
  candle_q_dim_analytic_jet_profile_event
    "variable-tree-topology-compute-end";
  if hyp topology_compute <> [] ||
     not (aconv (rand (concl topology_compute)) `Cexp_num 1`) then
    failwith "fixed outer variable tree prover: topology rejected";
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [result.variable_batch_prepared_source.expression_term;
         `ARB:real^6`;tree]
        candle_cv_q_dim_taylor_model_fixed_outer_variable_tree_compact_sound) in
  let premise =
    CONJ result.variable_batch_prepared_source.valid_theorem
      (CONJ tree_accept topology_compute) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer variable tree prover: soundness premise mismatch";
  let cell_theorem = MATCH_MP soundness premise in
  let source_theorem =
    REWRITE_RULE
      [m_cell_pass;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def;
       result.variable_batch_prepared_source.source_theorem]
      cell_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed outer variable tree prover: source assumptions";
  source_theorem;;

end;;
