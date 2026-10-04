(* ========================================================================== *)
(* Raw-data plan for the complete genuine action-296 right-hand certificate. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source program is authenticated once.    *)
(* Adaptive plans, boxes, and square-root intervals remain ordinary data for *)
(* the complete reflected checker to validate.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_action296_fixed_outer_generated_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_action296_variable_raw_plan = struct

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_action296_forest_plan;;
open Candle_cv_action296_fixed_outer_generated_plan;;

type candle_action296_variable_raw_root = {
  action296_variable_raw_root_index : int;
  action296_variable_raw_root_parent : thm;
  action296_variable_raw_root_tree : candle_action296_forest_tree;
  action296_variable_raw_root_domains : thm list;
  action296_variable_raw_root_box_intervals : term list;
  action296_variable_raw_root_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

type candle_action296_variable_raw_plan = {
  action296_variable_raw_plan_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  action296_variable_raw_plan_roots :
    candle_action296_variable_raw_root list;
  action296_variable_raw_plan_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

let candle_action296_variable_raw_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-variable-raw-plan" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_variable_raw_box_intervals point_plan parent =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds parent in
  let intervals =
    candle_q_box_rational_program_intervals_six
      point_plan.point_plan_programs lower upper in
  if length intervals <> 7 then
    failwith "action296 variable raw plan: whole-box slot drift";
  intervals;;

let candle_action296_variable_raw_cell point_plan box_intervals domain =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  if length center_intervals <> 7 then
    failwith "action296 variable raw plan: center slot drift";
  {
    variable_batch_box_intervals = box_intervals;
    variable_batch_stable_cell = {
      stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper;
    };
  };;

let rec candle_action296_variable_raw_reverse_append items result =
  match items with
  | [] -> result
  | head :: tail ->
      candle_action296_variable_raw_reverse_append tail (head :: result);;

let rec candle_action296_variable_raw_build
    point_plan expected roots parents roots_rev cells_rev =
  match roots,parents with
  | [],[] -> List.rev roots_rev,List.rev cells_rev
  | (index,plan_data) :: remaining_roots,
    parent :: remaining_parents ->
      if index <> expected then
        failwith "action296 variable raw plan: root order drift";
      let tree =
        candle_action296_forest_build_tree parent plan_data in
      let domains = candle_action296_forest_tree_domains tree in
      let box_intervals =
        candle_action296_variable_raw_box_intervals point_plan parent in
      let cells =
        map
          (candle_action296_variable_raw_cell point_plan box_intervals)
          domains in
      let root = {
        action296_variable_raw_root_index = index;
        action296_variable_raw_root_parent = parent;
        action296_variable_raw_root_tree = tree;
        action296_variable_raw_root_domains = domains;
        action296_variable_raw_root_box_intervals = box_intervals;
        action296_variable_raw_root_cells = cells;
      } in
      candle_action296_variable_raw_build point_plan
        (expected + 1) remaining_roots remaining_parents
        (root :: roots_rev)
        (candle_action296_variable_raw_reverse_append cells cells_rev)
  | _ -> failwith "action296 variable raw plan: root/parent shape drift";;

let candle_action296_variable_raw_plan_state :
    candle_action296_variable_raw_plan option ref = ref None;;

let _ =
  let axioms_before = axioms () in
  candle_action296_variable_raw_plan_marker "construction" "begin";
  let prepared = candle_action296_plan_prepared in
  let point_plan =
    candle_q_dim_taylor_model_point_plan_six prepared in
  let parents =
    candle_action296_leaf_grouping_collect
      candle_action296_leaf_grouping_root_domain
      candle_action296_plan_precision_tree in
  if length parents <> 1061 then
    failwith "action296 variable raw plan: parent cardinality drift";
  let roots,cells =
    candle_action296_variable_raw_build point_plan 0
      candle_action296_fixed_outer_generated_roots
      parents [] [] in
  if length roots <> 1061 ||
     length cells <> candle_action296_fixed_outer_generated_final_cells ||
     length cells <> 1538 ||
     hyp prepared.valid_theorem <> [] ||
     hyp prepared.source_theorem <> [] then
    failwith "action296 variable raw plan: complete shape drift";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "action296 variable raw plan: axiom-set drift";
  let plan = {
      action296_variable_raw_plan_prepared = prepared;
      action296_variable_raw_plan_roots = roots;
      action296_variable_raw_plan_cells = cells;
    } in
  candle_action296_variable_raw_plan_state := Some plan;
  candle_action296_variable_raw_plan_marker "construction" "end";
  print_endline
    "CANDLE_CV_ACTION296_VARIABLE_RAW_PLAN_OK DEVELOPMENT_NON_RELEASE roots=1061 cells=1538";;

let candle_action296_variable_raw_plan () =
  match !candle_action296_variable_raw_plan_state with
  | Some plan -> plan
  | None -> failwith "action296 variable raw plan: unavailable";;

end;;
