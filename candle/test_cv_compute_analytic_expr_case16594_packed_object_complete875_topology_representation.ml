(* ========================================================================== *)
(* Exact representation seam between the genuine packed-object jobs and the *)
(* already authenticated case-16594 axis plan.                               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This probe deliberately constructs, but does  *)
(* not reprove, the 875-cell geometry contract.  It is the cheap predecessor *)
(* to the integrated topology/root theorem.                                  *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_complete875_topology_representation = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support;;

let candle_case16594_complete875_topology_source_box job =
  let _,center_source = dest_pair job in
  let _,source_boxes = dest_pair center_source in
  source_boxes;;

let candle_case16594_complete875_topology_expected_source_box cell =
  let stable = cell.variable_batch_stable_cell in
  candle_poly_fixture_q_boxes
    stable.stable_batch_lower stable.stable_batch_upper;;

let candle_case16594_complete875_topology_radii_batches,
    candle_case16594_complete875_topology_jobs =
  candle_case16594_prefix_contract_data_with_radius_padding 1 875;;

let candle_case16594_complete875_topology_job_items =
  dest_list candle_case16594_complete875_topology_jobs;;

let candle_case16594_complete875_topology_source_boxes =
  map candle_case16594_complete875_topology_source_box
    candle_case16594_complete875_topology_job_items;;

let candle_case16594_complete875_topology_expected_source_boxes =
  map candle_case16594_complete875_topology_expected_source_box
    candle_disjunctive_case16594_variable_raw_plan_cells;;

let candle_case16594_complete875_topology_tokens =
  candle_disjunctive_case16594_compact_token_plan ();;

let candle_case16594_complete875_topology_token_items =
  dest_list candle_case16594_complete875_topology_tokens;;

let candle_case16594_complete875_topology_root_boxes =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds
      candle_disjunctive_case16594_root_domain in
  candle_poly_fixture_q_boxes lower upper;;

let candle_case16594_complete875_topology_first_mismatch left right =
  let rec compare index left right =
    match left,right with
    | [],[] -> None
    | left_head :: left_tail,right_head :: right_tail ->
        if aconv left_head right_head then
          compare (index + 1) left_tail right_tail
        else Some index
    | _ -> Some index in
  compare 0 left right;;

let _ =
  let source_count = length candle_case16594_complete875_topology_source_boxes
  and expected_count =
    length candle_case16594_complete875_topology_expected_source_boxes
  and token_count = length candle_case16594_complete875_topology_token_items in
  if source_count <> 875 || expected_count <> 875 || token_count <> 1749 ||
     candle_disjunctive_case16594_compact_token_leaf_count <> 875 ||
     candle_disjunctive_case16594_compact_token_glue_count <> 874 then
    failwith "case16594 complete875 topology representation: shape drift";
  (match
     candle_case16594_complete875_topology_first_mismatch
       candle_case16594_complete875_topology_source_boxes
       candle_case16594_complete875_topology_expected_source_boxes
   with
   | None -> ()
   | Some index ->
       failwith
         ("case16594 complete875 topology representation: source box " ^
          "mismatch at cell " ^ string_of_int index));
  print_endline
    "CANDLE_CV_CASE16594_PACKED_OBJECT_COMPLETE875_TOPOLOGY_REPRESENTATION_OK cells=875 leaf_tokens=875 glue_tokens=874 token_items=1749 source_box_identities=875 root_boxes=1 DEVELOPMENT_NON_RELEASE";;

end;;
