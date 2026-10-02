(* ========================================================================== *)
(* Proof-producing handoff for compact checked fixed-algebraic Taylor trees. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical batch theorem and the logical  *)
(* tree remain independently authenticated.  One reflected topology verdict *)
(* replaces the recursively constructed per-node well-formedness proof.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_algebraic_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

let candle_q_dim_taylor_model_tree_compact_prove_profile =
  ref (fun (_:string) -> ());;

let candle_q_dim_taylor_model_tree_compact_prove_event event =
  (!candle_q_dim_taylor_model_tree_compact_prove_profile) event;;

let candle_q_dim_taylor_model_tree_compact_topology_accept_six tree =
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_tree_topology_check`,
       [`Cexp_num 6`;
        mk_comb
          (`candle_cv_q_dim_taylor_model_tree_topology`,tree)]) in
  let representation =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_tree_topology_def;
       candle_cv_q_interval_list_def; candle_cv_q_interval_def;
       candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
      call in
  candle_q_dim_taylor_model_tree_compact_prove_event
    "topology-representation";
  let verdict =
    Kernel.compute
      (COMPUTE_INIT_THMS,
      candle_cv_q_dim_taylor_model_tree_compact_compute_eqs)
      (rand (concl representation)) in
  candle_q_dim_taylor_model_tree_compact_prove_event "topology-compute";
  if not (aconv (rand (concl verdict)) `Cexp_num 1`) then
    failwith "compact Taylor tree prover: topology rejected";
  let acceptance = TRANS representation verdict in
  candle_q_dim_taylor_model_tree_compact_prove_event "topology-linked";
  let expected =
    mk_eq
      (call,`Cexp_num 1`) in
  if hyp acceptance <> [] || not (aconv (concl acceptance) expected) then
    failwith "compact Taylor tree prover: malformed topology acceptance";
  acceptance;;

let candle_q_dim_taylor_model_fixed_algebraic_tree_compact_cell_six
    box_expression valid jobs accept tree =
  let jobs_call =
    mk_comb (`candle_q_dim_taylor_model_tree_jobs`,tree) in
  let jobs_expansion =
    REWRITE_CONV [candle_q_dim_taylor_model_tree_jobs_def;APPEND]
      jobs_call in
  candle_q_dim_taylor_model_tree_compact_prove_event "jobs-expanded";
  if hyp jobs_expansion <> [] ||
     not (aconv (rand (concl jobs_expansion)) jobs) then
    failwith "compact Taylor tree prover: tree/batch job mismatch";
  let tree_accept = REWRITE_RULE [SYM jobs_expansion] accept in
  candle_q_dim_taylor_model_tree_compact_prove_event "jobs-accepted";
  let topology =
    candle_q_dim_taylor_model_tree_compact_topology_accept_six tree in
  candle_q_dim_taylor_model_tree_compact_prove_event "topology-accepted";
  let soundness =
    REWRITE_RULE
      [Candle_cv_polynomial_expr_dim_jet_prove.
        candle_q_dim_poly_jet_dim_six]
      (ISPECL
        [box_expression;`ARB:real^6`;tree]
        candle_cv_q_dim_taylor_model_fixed_algebraic_tree_compact_sound) in
  candle_q_dim_taylor_model_tree_compact_prove_event
    "soundness-instantiated";
  let premise = CONJ valid (CONJ tree_accept topology) in
  candle_q_dim_taylor_model_tree_compact_prove_event "premise-built";
  if hyp valid <> [] || hyp accept <> [] ||
     not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "compact Taylor tree prover: soundness premise mismatch";
  let cell = MATCH_MP soundness premise in
  candle_q_dim_taylor_model_tree_compact_prove_event "cell-derived";
  if hyp cell <> [] then
    failwith "compact Taylor tree prover: cell theorem assumptions";
  cell;;

let candle_q_dim_taylor_model_fixed_algebraic_tree_compact_source_six
    (result:candle_q_dim_taylor_model_fixed_algebraic_batch_result_six)
    tree =
  let cell =
    candle_q_dim_taylor_model_fixed_algebraic_tree_compact_cell_six
      result.fixed_algebraic_batch_box_prepared.expression_term
      result.fixed_algebraic_batch_box_prepared.valid_theorem
      result.fixed_algebraic_batch_jobs_term
      result.fixed_algebraic_batch_accept_theorem tree in
  candle_q_dim_taylor_model_tree_compact_prove_event "source-cell-ready";
  let source =
    REWRITE_RULE
      [m_cell_pass;candle_q_dim_taylor_model_tree_root_boxes_def;
       result.fixed_algebraic_batch_box_prepared.source_theorem]
      cell in
  candle_q_dim_taylor_model_tree_compact_prove_event "source-rewritten";
  if hyp source <> [] then
    failwith "compact Taylor tree prover: source theorem assumptions";
  source;;

end;;
