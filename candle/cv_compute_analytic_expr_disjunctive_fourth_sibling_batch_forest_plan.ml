(* Mixed-disjunct forest plan for the fourth authentic sibling batch. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_depth2_scan.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_forest_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_axis1_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_remaining_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_depth2_scan;;

let candle_disjunctive_fourth_batch_one_level_selected =
  candle_disjunctive_fourth_batch_axis1_selected @
  candle_disjunctive_fourth_batch_remaining_selected;;

let candle_disjunctive_fourth_batch_one_level_axis
    record index selected =
  let rec find = function
    | [] -> None
    | (actual_record,actual_index,actual_selected,axis)::remaining ->
        if actual_record = record && actual_index = index &&
           actual_selected = selected
        then Some axis
        else find remaining in
  find candle_disjunctive_fourth_batch_one_level_selected;;

let candle_disjunctive_fourth_batch_depth2_first_axis
    record index selected =
  let rec find = function
    | [] -> None
    | (actual_record,actual_index,actual_selected,axis)::remaining ->
        if actual_record = record && actual_index = index &&
           actual_selected = selected
        then Some axis
        else find remaining in
  find candle_disjunctive_fourth_batch_depth2_first_plans;;

let candle_disjunctive_fourth_batch_depth2_second_axis
    record index selected first_axis first_side =
  let rec find = function
    | [] -> None
    | (actual_record,actual_index,actual_selected,actual_first_axis,
       actual_first_side,axis)::remaining ->
        if actual_record = record && actual_index = index &&
           actual_selected = selected && actual_first_axis = first_axis &&
           actual_first_side = first_side
        then Some axis
        else find remaining in
  find candle_disjunctive_fourth_batch_depth2_selected;;

let candle_disjunctive_fourth_batch_leaf selected domain =
  Candle_disjunctive_next_batch_leaf
    (selected,domain,candle_disjunctive_next_batch_cell selected domain);;

let candle_disjunctive_fourth_batch_depth2_side
    record index selected first_axis first_side domain =
  let failed =
    candle_disjunctive_fourth_batch_one_level_child_failed
      record index selected first_axis first_side in
  match
    failed,
    candle_disjunctive_fourth_batch_depth2_second_axis
      record index selected first_axis first_side
  with
  | false,None ->
      candle_disjunctive_fourth_batch_leaf selected domain,1,0
  | true,Some axis ->
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      Candle_disjunctive_next_batch_node
        (axis,domain,
         candle_disjunctive_fourth_batch_leaf selected left_domain,
         candle_disjunctive_fourth_batch_leaf selected right_domain),
      2,1
  | _ ->
      failwith "fourth sibling forest plan: depth2 selection drift";;

let rec candle_disjunctive_fourth_batch_shape_build
    record next_leaf domain tree =
  match tree with
  | P_result_pass (_,selected,raw_flag) ->
      if selected < 0 || selected > 1 || raw_flag then
        failwith "fourth sibling forest plan: pass selection drift";
      let source_leaf = next_leaf in
      (match candle_disjunctive_fourth_batch_depth2_first_axis
               record source_leaf selected with
       | Some first_axis ->
           let left_domain,right_domain =
             M_verifier.split_domain 6 6 first_axis domain in
           let left_shape,left_cells,left_glues =
             candle_disjunctive_fourth_batch_depth2_side
               record source_leaf selected first_axis 0 left_domain in
           let right_shape,right_cells,right_glues =
             candle_disjunctive_fourth_batch_depth2_side
               record source_leaf selected first_axis 1 right_domain in
           Candle_disjunctive_next_batch_node
             (first_axis,domain,left_shape,right_shape),
           source_leaf + 1,
           left_cells + right_cells,
           1 + left_glues + right_glues
       | None ->
           (match candle_disjunctive_fourth_batch_one_level_axis
                    record source_leaf selected with
            | Some axis ->
                let left_domain,right_domain =
                  M_verifier.split_domain 6 6 axis domain in
                Candle_disjunctive_next_batch_node
                  (axis,domain,
                   candle_disjunctive_fourth_batch_leaf
                     selected left_domain,
                   candle_disjunctive_fourth_batch_leaf
                     selected right_domain),
                source_leaf + 1,2,1
            | None ->
                candle_disjunctive_fourth_batch_leaf selected domain,
                source_leaf + 1,1,0))
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then failwith "fourth sibling forest plan: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left,left_cells,left_glues =
        candle_disjunctive_fourth_batch_shape_build
          record next_leaf left_domain left in
      let right_shape,after_right,right_cells,right_glues =
        candle_disjunctive_fourth_batch_shape_build
          record after_left right_domain right in
      Candle_disjunctive_next_batch_node
        (axis,domain,left_shape,right_shape),
      after_right,left_cells + right_cells,1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "fourth sibling forest plan: monotonicity node"
  | P_result_ref _ ->
      failwith "fourth sibling forest plan: reference node";;

let rec candle_disjunctive_fourth_batch_distinct = function
  | [] -> true
  | head::tail ->
      not (List.mem head tail) &&
      candle_disjunctive_fourth_batch_distinct tail;;

if length candle_disjunctive_fourth_batch_rejected <>
     length candle_disjunctive_fourth_batch_one_level_selected +
     length candle_disjunctive_fourth_batch_depth2_first_plans ||
   length candle_disjunctive_fourth_batch_depth2_first_plans <>
     length candle_disjunctive_fourth_batch_remaining_unsolved ||
   length candle_disjunctive_fourth_batch_depth2_selected <>
     length candle_disjunctive_fourth_batch_failed_first_children ||
   candle_disjunctive_fourth_batch_depth2_unsolved <> [] ||
   not
     (candle_disjunctive_fourth_batch_distinct
       candle_disjunctive_fourth_batch_one_level_selected) ||
   not
     (candle_disjunctive_fourth_batch_distinct
       candle_disjunctive_fourth_batch_depth2_first_plans) ||
   List.exists
     (fun (record,index,selected,_) ->
       candle_disjunctive_fourth_batch_depth2_first_axis
         record index selected <> None)
     candle_disjunctive_fourth_batch_one_level_selected then
  failwith "fourth sibling forest plan: refinement selection drift";;

let candle_disjunctive_case16364_shape,
    candle_disjunctive_case16364_after_leaf,
    candle_disjunctive_case16364_numerical_cells,
    candle_disjunctive_case16364_glue_nodes =
  candle_disjunctive_fourth_batch_shape_build
    16364 0 candle_disjunctive_case16364_root_domain
    candle_disjunctive_case16364_precision_tree;;
let candle_disjunctive_case16625_shape,
    candle_disjunctive_case16625_after_leaf,
    candle_disjunctive_case16625_numerical_cells,
    candle_disjunctive_case16625_glue_nodes =
  candle_disjunctive_fourth_batch_shape_build
    16625 0 candle_disjunctive_case16625_root_domain
    candle_disjunctive_case16625_precision_tree;;
let candle_disjunctive_case16587_shape,
    candle_disjunctive_case16587_after_leaf,
    candle_disjunctive_case16587_numerical_cells,
    candle_disjunctive_case16587_glue_nodes =
  candle_disjunctive_fourth_batch_shape_build
    16587 0 candle_disjunctive_case16587_root_domain
    candle_disjunctive_case16587_precision_tree;;

let candle_disjunctive_case16364_skeleton,
    candle_disjunctive_case16364_after_component,
    candle_disjunctive_case16364_components =
  candle_disjunctive_next_batch_skeletonize
    16364 0 candle_disjunctive_case16364_shape;;
let candle_disjunctive_case16625_skeleton,
    candle_disjunctive_case16625_after_component,
    candle_disjunctive_case16625_components =
  candle_disjunctive_next_batch_skeletonize
    16625 candle_disjunctive_case16364_after_component
    candle_disjunctive_case16625_shape;;
let candle_disjunctive_case16587_skeleton,
    candle_disjunctive_case16587_after_component,
    candle_disjunctive_case16587_components =
  candle_disjunctive_next_batch_skeletonize
    16587 candle_disjunctive_case16625_after_component
    candle_disjunctive_case16587_shape;;

let candle_disjunctive_fourth_batch_components =
  candle_disjunctive_case16364_components @
  candle_disjunctive_case16625_components @
  candle_disjunctive_case16587_components;;
let candle_disjunctive_fourth_batch_components0 =
  List.filter
    (fun component -> component.next_batch_component_selected = 0)
    candle_disjunctive_fourth_batch_components;;
let candle_disjunctive_fourth_batch_components1 =
  List.filter
    (fun component -> component.next_batch_component_selected = 1)
    candle_disjunctive_fourth_batch_components;;
let candle_disjunctive_fourth_batch_cells0,
    candle_disjunctive_fourth_batch_tokens0,
    candle_disjunctive_fourth_batch_expected_stack0 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_fourth_batch_components0;;
let candle_disjunctive_fourth_batch_cells1,
    candle_disjunctive_fourth_batch_tokens1,
    candle_disjunctive_fourth_batch_expected_stack1 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_fourth_batch_components1;;

let candle_disjunctive_fourth_batch_source_leaves =
  candle_disjunctive_case16364_leaf_count +
  candle_disjunctive_case16625_leaf_count +
  candle_disjunctive_case16587_leaf_count;;
let candle_disjunctive_fourth_batch_total_cells =
  candle_disjunctive_case16364_numerical_cells +
  candle_disjunctive_case16625_numerical_cells +
  candle_disjunctive_case16587_numerical_cells;;
let candle_disjunctive_fourth_batch_expected_cells =
  candle_disjunctive_fourth_batch_source_leaves +
  length candle_disjunctive_fourth_batch_one_level_selected +
  length candle_disjunctive_fourth_batch_depth2_first_plans +
  length candle_disjunctive_fourth_batch_depth2_selected;;
let candle_disjunctive_fourth_batch_total_tokens =
  length candle_disjunctive_fourth_batch_tokens0 +
  length candle_disjunctive_fourth_batch_tokens1;;

if candle_disjunctive_fourth_batch_source_leaves <> 13978 ||
   candle_disjunctive_case16364_after_leaf <>
     candle_disjunctive_case16364_leaf_count ||
   candle_disjunctive_case16625_after_leaf <>
     candle_disjunctive_case16625_leaf_count ||
   candle_disjunctive_case16587_after_leaf <>
     candle_disjunctive_case16587_leaf_count ||
   candle_disjunctive_fourth_batch_total_cells <>
     candle_disjunctive_fourth_batch_expected_cells ||
   candle_disjunctive_case16587_after_component <>
     length candle_disjunctive_fourth_batch_components ||
   length candle_disjunctive_fourth_batch_cells0 +
     length candle_disjunctive_fourth_batch_cells1 <>
     candle_disjunctive_fourth_batch_total_cells ||
   candle_disjunctive_fourth_batch_total_tokens <>
     2 * candle_disjunctive_fourth_batch_total_cells -
     length candle_disjunctive_fourth_batch_components then
  failwith "fourth sibling forest plan: final accounting drift";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FOREST_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " source_leaves=" ^
   string_of_int candle_disjunctive_fourth_batch_source_leaves ^
   " numerical_cells=" ^
   string_of_int candle_disjunctive_fourth_batch_total_cells ^
   " components=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components) ^
   " function0_components=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components0) ^
   " function1_components=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components1) ^
   " function0_cells=" ^
   string_of_int (length candle_disjunctive_fourth_batch_cells0) ^
   " function1_cells=" ^
   string_of_int (length candle_disjunctive_fourth_batch_cells1) ^
   " token_items=" ^
   string_of_int candle_disjunctive_fourth_batch_total_tokens ^
   " numerical_programs=2");;

end;;
