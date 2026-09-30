(* One genuine case16594 fallback split through the compact root path. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_variable_tree_split = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_prove;;

let candle_disjunctive_case16594_variable_tree_split_axioms_before =
  axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-tree-split" ^
       " phase=" ^ event));;

let candle_disjunctive_case16594_variable_tree_split_selected,
    candle_disjunctive_case16594_variable_tree_split_domain =
  List.nth
    candle_disjunctive_case16594_engine_state.family_engine_leaves 388;;
let candle_disjunctive_case16594_variable_tree_split_left_domain,
    candle_disjunctive_case16594_variable_tree_split_right_domain =
  M_verifier.split_domain 6 6 1
    candle_disjunctive_case16594_variable_tree_split_domain;;

if candle_disjunctive_case16594_variable_tree_split_selected <> 1 then
  failwith "case16594 variable tree split: selection drift";;

let candle_disjunctive_case16594_variable_tree_split_cell domain =
  let lower,upper = candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16594_engine_state.family_engine_point_plan
      lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_case16594_variable_tree_split_cells =
  [candle_disjunctive_case16594_variable_tree_split_cell
     candle_disjunctive_case16594_variable_tree_split_left_domain;
   candle_disjunctive_case16594_variable_tree_split_cell
     candle_disjunctive_case16594_variable_tree_split_right_domain];;
let candle_disjunctive_case16594_variable_tree_split_batch =
  candle_q_dim_taylor_model_fixed_outer_variable_batch_prove_six
    candle_disjunctive_case16594_engine_state.family_engine_prepared
    candle_disjunctive_case16594_variable_tree_split_cells;;

let candle_disjunctive_case16594_variable_tree_split_leaf prepared =
  let stable = prepared.variable_batch_stable_prepared_cell in
  list_mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf`,
     [prepared.variable_batch_box_intervals_term;
      stable.stable_batch_center_intervals_term;
      stable.stable_batch_boxes_term]);;

let candle_disjunctive_case16594_variable_tree_split_prepared =
  candle_disjunctive_case16594_variable_tree_split_batch.
    variable_batch_prepared_cells;;
let candle_disjunctive_case16594_variable_tree_split_left =
  candle_disjunctive_case16594_variable_tree_split_leaf
    (List.nth candle_disjunctive_case16594_variable_tree_split_prepared 0);;
let candle_disjunctive_case16594_variable_tree_split_right =
  candle_disjunctive_case16594_variable_tree_split_leaf
    (List.nth candle_disjunctive_case16594_variable_tree_split_prepared 1);;
let candle_disjunctive_case16594_variable_tree_split_lower,
    candle_disjunctive_case16594_variable_tree_split_upper =
  candle_disjunctive_fixed_outer_domain_bounds
    candle_disjunctive_case16594_variable_tree_split_domain;;
let candle_disjunctive_case16594_variable_tree_split_boxes =
  candle_poly_fixture_q_boxes
    candle_disjunctive_case16594_variable_tree_split_lower
    candle_disjunctive_case16594_variable_tree_split_upper;;
let candle_disjunctive_case16594_variable_tree_split_tree =
  list_mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_tree_node`,
     [`1`;candle_disjunctive_case16594_variable_tree_split_boxes;
      candle_disjunctive_case16594_variable_tree_split_left;
      candle_disjunctive_case16594_variable_tree_split_right]);;
let candle_disjunctive_case16594_variable_tree_split_source =
  candle_q_dim_taylor_model_fixed_outer_variable_tree_source_six
    candle_disjunctive_case16594_variable_tree_split_batch
    candle_disjunctive_case16594_variable_tree_split_tree;;

let candle_disjunctive_case16594_variable_tree_split_theorem =
  candle_reflected_nl_source_pass_with
    candle_disjunctive_case16594_engine_state.family_engine_function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_fixed_outer_aconv_lists
             actual_lower
             candle_disjunctive_case16594_variable_tree_split_lower &&
           candle_disjunctive_fixed_outer_aconv_lists
             actual_upper
             candle_disjunctive_case16594_variable_tree_split_upper) then
        failwith "case16594 variable tree split: handoff box drift";
      candle_disjunctive_case16594_variable_tree_split_source)
    candle_disjunctive_case16594_variable_tree_split_domain;;

let candle_disjunctive_case16594_variable_tree_split_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm
        candle_disjunctive_case16594_variable_tree_split_theorem));;
let candle_disjunctive_case16594_variable_tree_split_axioms_after =
  axioms ();;

if hyp candle_disjunctive_case16594_variable_tree_split_theorem <> [] ||
   candle_disjunctive_case16594_variable_tree_split_digest <>
     "a9998d9789b7673c2b7d1ab389c83831" ||
   length candle_disjunctive_case16594_variable_tree_split_axioms_after <>
     length candle_disjunctive_case16594_variable_tree_split_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_disjunctive_case16594_variable_tree_split_axioms_before)
       candle_disjunctive_case16594_variable_tree_split_axioms_after) then
  failwith "case16594 variable tree split: final validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TREE_SPLIT_RESULT" ^
   " original_leaf=388 cells=2 glue_nodes=1" ^
   " numerical_computes=1 topology_computes=1 root_handoffs=1" ^
   " theorem_digest=" ^
   candle_disjunctive_case16594_variable_tree_split_digest);;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TREE_SPLIT_OK DEVELOPMENT_NON_RELEASE";;

end;;
