(* ========================================================================== *)
(* Proof-producing handoff for exact centered-Taylor split trees.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical work remains the single batch  *)
(* Kernel.compute verdict.  This adapter authenticates that the batch jobs   *)
(* are exactly the leaves of a proved split tree and returns one source      *)
(* theorem over the tree's root box.                                         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;

let candle_q_dim_taylor_model_tree_leaf_term center_e boxes =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_leaf`,[center_e;boxes]);;

let candle_q_dim_taylor_model_tree_node_term split_index boxes left right =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_node`,
     [split_index;boxes;left;right]);;

let candle_q_dim_taylor_model_tree_source_six
    (result:candle_q_dim_taylor_model_batch_result_six)
    tree well_formed =
  let jobs_call =
    mk_comb (`candle_q_dim_taylor_model_tree_jobs`,tree) in
  let jobs_expansion =
    REWRITE_CONV [candle_q_dim_taylor_model_tree_jobs_def;APPEND]
      jobs_call in
  if hyp jobs_expansion <> [] ||
     not (aconv (rand (concl jobs_expansion)) result.batch_jobs_term) then
    failwith "certified Taylor tree prover: tree/batch job mismatch";
  let tree_accept =
    REWRITE_RULE [SYM jobs_expansion] result.batch_accept_theorem in
  let well_formed_goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;tree]) in
  if hyp well_formed <> [] ||
     not (aconv (concl well_formed) well_formed_goal) then
    failwith "certified Taylor tree prover: malformed topology theorem";
  let soundness =
    REWRITE_RULE
      [Candle_cv_polynomial_expr_dim_jet_prove.candle_q_dim_poly_jet_dim_six]
      (ISPECL
        [result.batch_box_prepared.expression_term;`ARB:real^6`;tree]
        candle_q_dim_taylor_model_tree_sound) in
  let premise =
    CONJ result.batch_box_prepared.valid_theorem
      (CONJ tree_accept well_formed) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "certified Taylor tree prover: soundness premise mismatch";
  let cell_theorem = MATCH_MP soundness premise in
  let source_theorem =
    REWRITE_RULE
      [m_cell_pass;candle_q_dim_taylor_model_tree_root_boxes_def;
       result.batch_box_prepared.source_theorem]
      cell_theorem in
  if hyp source_theorem <> [] then
    failwith "certified Taylor tree prover: source theorem assumptions";
  source_theorem;;

end;;
