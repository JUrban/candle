(* ========================================================================== *)
(* Proof-producing handoff for fixed-hybrid exact split trees.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_tree.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_tree_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_tree;;

let candle_q_dim_taylor_model_fixed_tree_source_six
    (result:candle_q_dim_taylor_model_fixed_batch_result_six)
    tree well_formed =
  let jobs_call =
    mk_comb (`candle_q_dim_taylor_model_tree_jobs`,tree) in
  let jobs_expansion =
    REWRITE_CONV [candle_q_dim_taylor_model_tree_jobs_def;APPEND]
      jobs_call in
  if hyp jobs_expansion <> [] ||
     not
       (aconv (rand (concl jobs_expansion))
         result.fixed_batch_jobs_term) then
    failwith "fixed Taylor tree prover: tree/batch job mismatch";
  let tree_accept =
    REWRITE_RULE [SYM jobs_expansion]
      result.fixed_batch_accept_theorem in
  let well_formed_goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;tree]) in
  if hyp well_formed <> [] ||
     not (aconv (concl well_formed) well_formed_goal) then
    failwith "fixed Taylor tree prover: malformed topology theorem";
  let soundness =
    REWRITE_RULE
      [Candle_cv_polynomial_expr_dim_jet_prove.
        candle_q_dim_poly_jet_dim_six]
      (ISPECL
        [result.fixed_batch_box_prepared.expression_term;
         `ARB:real^6`;tree]
        candle_q_dim_taylor_model_fixed_tree_sound) in
  let premise =
    CONJ result.fixed_batch_box_prepared.valid_theorem
      (CONJ tree_accept well_formed) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed Taylor tree prover: soundness premise mismatch";
  let cell_theorem = MATCH_MP soundness premise in
  let source_theorem =
    REWRITE_RULE
      [m_cell_pass;candle_q_dim_taylor_model_tree_root_boxes_def;
       result.fixed_batch_box_prepared.source_theorem]
      cell_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed Taylor tree prover: source theorem assumptions";
  source_theorem;;

end;;
