(* ========================================================================== *)
(* Stable-program/raw-data plan for the complete genuine case-10173 forest. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The authenticated source expression and       *)
(* point plan are shared with action 296.  The already discovered case-10173 *)
(* forest supplies ordinary box and square-root certificate data.  This file *)
(* constructs no numerical acceptance or source theorem by itself.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_action296_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_case10173_fixed_outer_generated_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan = struct

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_reused_plan;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_action296_forest_plan;;
open Candle_cv_polynomial_expr_flyspeck_reify;;

type candle_case10173_variable_raw_root = {
  case10173_variable_raw_root_index : int;
  case10173_variable_raw_root_parent : thm;
  case10173_variable_raw_root_tree : candle_action296_forest_tree;
  case10173_variable_raw_root_domains : thm list;
  case10173_variable_raw_root_box_intervals : term list;
  case10173_variable_raw_root_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

type candle_case10173_variable_raw_plan = {
  case10173_variable_raw_plan_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  case10173_variable_raw_plan_roots :
    candle_case10173_variable_raw_root list;
  case10173_variable_raw_plan_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

let candle_case10173_variable_raw_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=case10173-variable-raw-plan" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let candle_case10173_variable_raw_prepare () =
  let function_term = candle_case10173_analytic_function in
  let vector,_ = dest_abs function_term in
  let variables = candle_poly_vector_components vector 6 in
  let variable_square_roots =
    map (fun variable -> mk_comb (`sqrt:real->real`,variable)) variables in
  let variable_count = ref 0 and nested_count = ref 0 in
  let square_root_interval square_root =
    if exists (aconv square_root) variable_square_roots then begin
      variable_count := !variable_count + 1;
      `((((2,0),0),((3,0),0)):
        ((num#num)#num)#((num#num)#num))`
    end else begin
      nested_count := !nested_count + 1;
      `((((50,0),0),((100,0),0)):
        ((num#num)#num)#((num#num)#num))`
    end in
  let prepared =
    candle_q_dim_analytic_jet_prepare_six_with
      square_root_interval function_term in
  if !variable_count <> 6 || !nested_count <> 1 ||
     length (dest_list prepared.program_term) <> 54 ||
     hyp prepared.valid_theorem <> [] ||
     hyp prepared.source_theorem <> [] then
    failwith "case10173 variable raw plan: source preparation drift";
  prepared;;

let candle_case10173_variable_raw_box_intervals point_plan parent =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds parent in
  let intervals =
    candle_q_box_rational_program_intervals_six
      point_plan.point_plan_programs lower upper in
  if length intervals <> 7 then
    failwith "case10173 variable raw plan: whole-box slot drift";
  intervals;;

let candle_case10173_variable_raw_cell point_plan box_intervals domain =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  if length center_intervals <> 7 then
    failwith "case10173 variable raw plan: center slot drift";
  {
    variable_batch_box_intervals = box_intervals;
    variable_batch_stable_cell = {
      stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper;
    };
  };;

let rec candle_case10173_variable_raw_reverse_append items result =
  match items with
  | [] -> result
  | head :: tail ->
      candle_case10173_variable_raw_reverse_append tail (head :: result);;

let rec candle_case10173_variable_raw_build
    point_plan expected roots parents roots_rev cells_rev =
  match roots,parents with
  | [],[] -> List.rev roots_rev,List.rev cells_rev
  | (index,plan_data) :: remaining_roots,
    parent :: remaining_parents ->
      if index <> expected then
        failwith "case10173 variable raw plan: root order drift";
      let tree =
        candle_action296_forest_build_tree parent plan_data in
      let domains = candle_action296_forest_tree_domains tree in
      let box_intervals =
        candle_case10173_variable_raw_box_intervals
          point_plan parent in
      let cells =
        map
          (candle_case10173_variable_raw_cell
            point_plan box_intervals)
          domains in
      let root = {
        case10173_variable_raw_root_index = index;
        case10173_variable_raw_root_parent = parent;
        case10173_variable_raw_root_tree = tree;
        case10173_variable_raw_root_domains = domains;
        case10173_variable_raw_root_box_intervals = box_intervals;
        case10173_variable_raw_root_cells = cells;
      } in
      candle_case10173_variable_raw_build point_plan
        (expected + 1) remaining_roots remaining_parents
        (root :: roots_rev)
        (candle_case10173_variable_raw_reverse_append cells cells_rev)
  | _ -> failwith "case10173 variable raw plan: root/parent shape drift";;

let candle_case10173_variable_raw_plan_state :
    candle_case10173_variable_raw_plan option ref = ref None;;

let _ =
  let axioms_before = axioms () in
  candle_case10173_variable_raw_plan_marker "construction" "begin";
  let prepared = candle_case10173_variable_raw_prepare () in
  let point_plan =
    candle_q_dim_taylor_model_point_plan_six
      prepared in
  let roots,cells =
    candle_case10173_variable_raw_build point_plan 0
      candle_action296_generated_roots
      !candle_action296_leaf_grouping_leaves [] [] in
  if length roots <> 3305 ||
     length cells <> candle_action296_generated_final_cells ||
     length cells <> 4173 then
    failwith "case10173 variable raw plan: complete shape drift";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "case10173 variable raw plan: axiom-set drift";
  let plan = {
      case10173_variable_raw_plan_prepared = prepared;
      case10173_variable_raw_plan_roots = roots;
      case10173_variable_raw_plan_cells = cells;
    } in
  candle_case10173_variable_raw_plan_state := Some plan;
  candle_case10173_variable_raw_plan_marker "construction" "end";
  print_endline
    "CANDLE_CV_CASE10173_VARIABLE_RAW_PLAN_OK DEVELOPMENT_NON_RELEASE roots=3305 cells=4173";;

let candle_case10173_variable_raw_plan () =
  match !candle_case10173_variable_raw_plan_state with
  | Some plan -> plan
  | None -> failwith "case10173 variable raw plan: unavailable";;

end;;
