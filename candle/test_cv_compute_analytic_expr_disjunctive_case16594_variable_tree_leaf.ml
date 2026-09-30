(* One genuine case16594 leaf through the compact variable-tree root path. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_variable_tree_leaf = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_prove;;

let candle_disjunctive_case16594_variable_tree_leaf_axioms_before =
  axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-tree-leaf" ^
       " phase=" ^ event));;

let candle_disjunctive_case16594_variable_tree_leaf_selected,
    candle_disjunctive_case16594_variable_tree_leaf_domain =
  hd candle_disjunctive_case16594_engine_state.family_engine_leaves;;

if candle_disjunctive_case16594_variable_tree_leaf_selected <> 1 then
  failwith "case16594 variable tree leaf: selection drift";;

let candle_disjunctive_case16594_variable_tree_leaf_lower,
    candle_disjunctive_case16594_variable_tree_leaf_upper =
  candle_disjunctive_fixed_outer_domain_bounds
    candle_disjunctive_case16594_variable_tree_leaf_domain;;
let candle_disjunctive_case16594_variable_tree_leaf_center =
  candle_q_dim_taylor_model_point_plan_intervals_six
    candle_disjunctive_case16594_engine_state.family_engine_point_plan
    candle_disjunctive_case16594_variable_tree_leaf_lower
    candle_disjunctive_case16594_variable_tree_leaf_upper;;
let candle_disjunctive_case16594_variable_tree_leaf_box =
  map
    (candle_disjunctive_fixed_outer_widen 5 4)
    candle_disjunctive_case16594_variable_tree_leaf_center;;
let candle_disjunctive_case16594_variable_tree_leaf_cell =
  {variable_batch_box_intervals =
     candle_disjunctive_case16594_variable_tree_leaf_box;
   variable_batch_stable_cell =
     {stable_batch_center_intervals =
        candle_disjunctive_case16594_variable_tree_leaf_center;
      stable_batch_lower =
        candle_disjunctive_case16594_variable_tree_leaf_lower;
      stable_batch_upper =
        candle_disjunctive_case16594_variable_tree_leaf_upper}};;

let candle_disjunctive_case16594_variable_tree_leaf_batch =
  candle_q_dim_taylor_model_fixed_outer_variable_batch_prove_six
    candle_disjunctive_case16594_engine_state.family_engine_prepared
    [candle_disjunctive_case16594_variable_tree_leaf_cell];;
let candle_disjunctive_case16594_variable_tree_leaf_prepared =
  hd
    candle_disjunctive_case16594_variable_tree_leaf_batch.
      variable_batch_prepared_cells;;
let candle_disjunctive_case16594_variable_tree_leaf_stable =
  candle_disjunctive_case16594_variable_tree_leaf_prepared.
    variable_batch_stable_prepared_cell;;
let candle_disjunctive_case16594_variable_tree_leaf_tree =
  list_mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf`,
     [candle_disjunctive_case16594_variable_tree_leaf_prepared.
        variable_batch_box_intervals_term;
      candle_disjunctive_case16594_variable_tree_leaf_stable.
        stable_batch_center_intervals_term;
      candle_disjunctive_case16594_variable_tree_leaf_stable.
        stable_batch_boxes_term]);;
let candle_disjunctive_case16594_variable_tree_leaf_source =
  candle_q_dim_taylor_model_fixed_outer_variable_tree_source_six
    candle_disjunctive_case16594_variable_tree_leaf_batch
    candle_disjunctive_case16594_variable_tree_leaf_tree;;

let candle_disjunctive_case16594_variable_tree_leaf_theorem =
  candle_reflected_nl_source_pass_with
    candle_disjunctive_case16594_engine_state.family_engine_function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_fixed_outer_aconv_lists
             actual_lower
             candle_disjunctive_case16594_variable_tree_leaf_lower &&
           candle_disjunctive_fixed_outer_aconv_lists
             actual_upper
             candle_disjunctive_case16594_variable_tree_leaf_upper) then
        failwith "case16594 variable tree leaf: handoff box drift";
      candle_disjunctive_case16594_variable_tree_leaf_source)
    candle_disjunctive_case16594_variable_tree_leaf_domain;;

let candle_disjunctive_case16594_variable_tree_leaf_functions,
    candle_disjunctive_case16594_variable_tree_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_disjunctive_case16594_variable_tree_leaf_theorem);;
let candle_disjunctive_case16594_variable_tree_leaf_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm
        candle_disjunctive_case16594_variable_tree_leaf_theorem));;
let candle_disjunctive_case16594_variable_tree_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_disjunctive_case16594_variable_tree_leaf_domain);;
let candle_disjunctive_case16594_variable_tree_leaf_axioms_after =
  axioms ();;

if candle_disjunctive_case16594_variable_tree_leaf_functions <>
     [candle_disjunctive_case16594_engine_state.
        family_engine_function_term] ||
   not
     (aconv candle_disjunctive_case16594_variable_tree_leaf_proved_domain
       candle_disjunctive_case16594_variable_tree_leaf_expected_domain) ||
   hyp candle_disjunctive_case16594_variable_tree_leaf_theorem <> [] ||
   candle_disjunctive_case16594_variable_tree_leaf_digest <>
     "e80cb255c7c75a970946d4e7d8567688" ||
   length candle_disjunctive_case16594_variable_tree_leaf_axioms_after <>
     length candle_disjunctive_case16594_variable_tree_leaf_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_disjunctive_case16594_variable_tree_leaf_axioms_before)
       candle_disjunctive_case16594_variable_tree_leaf_axioms_after) then
  failwith "case16594 variable tree leaf: final validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TREE_LEAF_RESULT" ^
   " cells=1 numerical_computes=1 topology_computes=1 root_handoffs=1" ^
   " theorem_digest=" ^
   candle_disjunctive_case16594_variable_tree_leaf_digest);;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TREE_LEAF_OK DEVELOPMENT_NON_RELEASE";;

end;;
