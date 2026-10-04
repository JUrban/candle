(* ========================================================================== *)
(* Mixed-disjunct forest plan for the next authentic production sibling batch. *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_remaining_split_scan.ml";;

module Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan = struct

open Certificate;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_remaining_split_scan;;

type candle_disjunctive_next_batch_shape =
  | Candle_disjunctive_next_batch_leaf of
      int * thm *
      candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six
  | Candle_disjunctive_next_batch_node of
      int * thm * candle_disjunctive_next_batch_shape *
      candle_disjunctive_next_batch_shape;;

type candle_disjunctive_next_batch_component = {
  next_batch_component_id : int;
  next_batch_component_record : int;
  next_batch_component_selected : int;
  next_batch_component_domain : thm;
  next_batch_component_shape : candle_disjunctive_next_batch_shape;
};;

type candle_disjunctive_next_batch_skeleton =
  | Candle_disjunctive_next_batch_component of int
  | Candle_disjunctive_next_batch_mixed of
      int * candle_disjunctive_next_batch_skeleton *
      candle_disjunctive_next_batch_skeleton;;

type candle_disjunctive_next_batch_token =
  | Candle_disjunctive_next_batch_token_leaf
  | Candle_disjunctive_next_batch_token_glue of int;;

let candle_disjunctive_next_batch_split_axis record index selected =
  let rec find = function
    | [] -> None
    | (actual_record,actual_index,actual_selected,axis)::remaining ->
        if actual_record = record && actual_index = index &&
           actual_selected = selected
        then Some axis
        else find remaining in
  find candle_disjunctive_next_batch_split_selected_complete;;

let candle_disjunctive_next_batch_cell selected domain =
  let point_plan =
    if selected = 0 then candle_disjunctive_next_batch_point_plan0
    else if selected = 1 then candle_disjunctive_next_batch_point_plan1
    else failwith "next sibling forest plan: invalid selection" in
  candle_disjunctive_next_batch_scan_cell point_plan domain;;

let rec candle_disjunctive_next_batch_shape_build
    record next_leaf domain tree =
  match tree with
  | P_result_pass (_,selected,raw_flag) ->
      if selected < 0 || selected > 1 || raw_flag then
        failwith "next sibling forest plan: pass selection drift";
      let source_leaf = next_leaf in
      (match candle_disjunctive_next_batch_split_axis
               record source_leaf selected with
       | Some axis ->
           let left_domain,right_domain =
             M_verifier.split_domain 6 6 axis domain in
           Candle_disjunctive_next_batch_node
             (axis,domain,
              Candle_disjunctive_next_batch_leaf
                (selected,left_domain,
                 candle_disjunctive_next_batch_cell selected left_domain),
              Candle_disjunctive_next_batch_leaf
                (selected,right_domain,
                 candle_disjunctive_next_batch_cell selected right_domain)),
           source_leaf + 1,2,1
       | None ->
           Candle_disjunctive_next_batch_leaf
             (selected,domain,
              candle_disjunctive_next_batch_cell selected domain),
           source_leaf + 1,1,0)
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then failwith "next sibling forest plan: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left,left_cells,left_glues =
        candle_disjunctive_next_batch_shape_build
          record next_leaf left_domain left in
      let right_shape,after_right,right_cells,right_glues =
        candle_disjunctive_next_batch_shape_build
          record after_left right_domain right in
      Candle_disjunctive_next_batch_node
        (axis,domain,left_shape,right_shape),
      after_right,left_cells + right_cells,1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "next sibling forest plan: monotonicity node"
  | P_result_ref _ ->
      failwith "next sibling forest plan: reference node";;

let candle_disjunctive_next_batch_shape_domain = function
  | Candle_disjunctive_next_batch_leaf (_,domain,_) -> domain
  | Candle_disjunctive_next_batch_node (_,domain,_,_) -> domain;;

let rec candle_disjunctive_next_batch_shape_selection = function
  | Candle_disjunctive_next_batch_leaf (selected,_,_) -> Some selected
  | Candle_disjunctive_next_batch_node (_,_,left,right) ->
      (match candle_disjunctive_next_batch_shape_selection left,
             candle_disjunctive_next_batch_shape_selection right with
       | Some left_selected,Some right_selected
           when left_selected = right_selected -> Some left_selected
       | _ -> None);;

let rec candle_disjunctive_next_batch_skeletonize
    record next_component shape =
  match candle_disjunctive_next_batch_shape_selection shape with
  | Some selected ->
      let component =
        {next_batch_component_id = next_component;
         next_batch_component_record = record;
         next_batch_component_selected = selected;
         next_batch_component_domain =
           candle_disjunctive_next_batch_shape_domain shape;
         next_batch_component_shape = shape} in
      Candle_disjunctive_next_batch_component next_component,
      next_component + 1,[component]
  | None ->
      (match shape with
       | Candle_disjunctive_next_batch_node (axis,_,left,right) ->
           let left_skeleton,after_left,left_components =
             candle_disjunctive_next_batch_skeletonize
               record next_component left in
           let right_skeleton,after_right,right_components =
             candle_disjunctive_next_batch_skeletonize
               record after_left right in
           Candle_disjunctive_next_batch_mixed
             (axis,left_skeleton,right_skeleton),
           after_right,left_components @ right_components
       | Candle_disjunctive_next_batch_leaf _ ->
           failwith "next sibling forest plan: mixed leaf");;

let rec candle_disjunctive_next_batch_shape_cells = function
  | Candle_disjunctive_next_batch_leaf (_,_,cell) -> [cell]
  | Candle_disjunctive_next_batch_node (_,_,left,right) ->
      candle_disjunctive_next_batch_shape_cells left @
      candle_disjunctive_next_batch_shape_cells right;;

let rec candle_disjunctive_next_batch_shape_tokens = function
  | Candle_disjunctive_next_batch_leaf _ ->
      [Candle_disjunctive_next_batch_token_leaf]
  | Candle_disjunctive_next_batch_node (axis,_,left,right) ->
      candle_disjunctive_next_batch_shape_tokens left @
      candle_disjunctive_next_batch_shape_tokens right @
      [Candle_disjunctive_next_batch_token_glue axis];;

let candle_disjunctive_next_batch_component_boxes component =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds
      component.next_batch_component_domain in
  candle_poly_fixture_q_boxes lower upper;;

let candle_disjunctive_next_batch_encode_token = function
  | Candle_disjunctive_next_batch_token_leaf -> `Cexp_num 0`
  | Candle_disjunctive_next_batch_token_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let candle_disjunctive_next_batch_logical_token = function
  | Candle_disjunctive_next_batch_token_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_next_batch_token_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let candle_disjunctive_next_batch_forest components =
  let cells =
    List.flatten
      (map
        (fun component ->
          candle_disjunctive_next_batch_shape_cells
            component.next_batch_component_shape)
        components) in
  let tokens =
    List.flatten
      (map
        (fun component ->
          candle_disjunctive_next_batch_shape_tokens
            component.next_batch_component_shape)
        components) in
  let expected_stack_boxes =
    rev (map candle_disjunctive_next_batch_component_boxes components) in
  cells,tokens,expected_stack_boxes;;

if candle_disjunctive_next_batch_split_unsolved_complete <> [] then
  failwith "next sibling forest plan: unresolved retry leaf";;

let candle_disjunctive_case16617_shape,
    candle_disjunctive_case16617_after_leaf,
    candle_disjunctive_case16617_numerical_cells,
    candle_disjunctive_case16617_glue_nodes =
  candle_disjunctive_next_batch_shape_build
    16617 0 candle_disjunctive_case16617_root_domain
    candle_disjunctive_case16617_precision_tree;;
let candle_disjunctive_case16593_shape,
    candle_disjunctive_case16593_after_leaf,
    candle_disjunctive_case16593_numerical_cells,
    candle_disjunctive_case16593_glue_nodes =
  candle_disjunctive_next_batch_shape_build
    16593 0 candle_disjunctive_case16593_root_domain
    candle_disjunctive_case16593_precision_tree;;
let candle_disjunctive_case16582_shape,
    candle_disjunctive_case16582_after_leaf,
    candle_disjunctive_case16582_numerical_cells,
    candle_disjunctive_case16582_glue_nodes =
  candle_disjunctive_next_batch_shape_build
    16582 0 candle_disjunctive_case16582_root_domain
    candle_disjunctive_case16582_precision_tree;;

let candle_disjunctive_case16617_skeleton,
    candle_disjunctive_case16617_after_component,
    candle_disjunctive_case16617_components =
  candle_disjunctive_next_batch_skeletonize
    16617 0 candle_disjunctive_case16617_shape;;
let candle_disjunctive_case16593_skeleton,
    candle_disjunctive_case16593_after_component,
    candle_disjunctive_case16593_components =
  candle_disjunctive_next_batch_skeletonize
    16593 candle_disjunctive_case16617_after_component
    candle_disjunctive_case16593_shape;;
let candle_disjunctive_case16582_skeleton,
    candle_disjunctive_case16582_after_component,
    candle_disjunctive_case16582_components =
  candle_disjunctive_next_batch_skeletonize
    16582 candle_disjunctive_case16593_after_component
    candle_disjunctive_case16582_shape;;

let candle_disjunctive_next_batch_components =
  candle_disjunctive_case16617_components @
  candle_disjunctive_case16593_components @
  candle_disjunctive_case16582_components;;
let candle_disjunctive_next_batch_components0 =
  List.filter
    (fun component -> component.next_batch_component_selected = 0)
    candle_disjunctive_next_batch_components;;
let candle_disjunctive_next_batch_components1 =
  List.filter
    (fun component -> component.next_batch_component_selected = 1)
    candle_disjunctive_next_batch_components;;
let candle_disjunctive_next_batch_cells0,
    candle_disjunctive_next_batch_tokens0,
    candle_disjunctive_next_batch_expected_stack0 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_next_batch_components0;;
let candle_disjunctive_next_batch_cells1,
    candle_disjunctive_next_batch_tokens1,
    candle_disjunctive_next_batch_expected_stack1 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_next_batch_components1;;

let candle_disjunctive_next_batch_total_cells =
  candle_disjunctive_case16617_numerical_cells +
  candle_disjunctive_case16593_numerical_cells +
  candle_disjunctive_case16582_numerical_cells;;
let candle_disjunctive_next_batch_total_tokens =
  length candle_disjunctive_next_batch_tokens0 +
  length candle_disjunctive_next_batch_tokens1;;

if candle_disjunctive_case16617_after_leaf <>
     candle_disjunctive_case16617_leaf_count ||
   candle_disjunctive_case16593_after_leaf <>
     candle_disjunctive_case16593_leaf_count ||
   candle_disjunctive_case16582_after_leaf <>
     candle_disjunctive_case16582_leaf_count ||
   candle_disjunctive_case16582_after_component <>
     length candle_disjunctive_next_batch_components ||
   length candle_disjunctive_next_batch_cells0 +
     length candle_disjunctive_next_batch_cells1 <>
     candle_disjunctive_next_batch_total_cells ||
   candle_disjunctive_next_batch_total_tokens <>
     2 * candle_disjunctive_next_batch_total_cells -
     length candle_disjunctive_next_batch_components then
  failwith "next sibling forest plan: final accounting drift";;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_FOREST_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " source_leaves=" ^
   string_of_int
     (candle_disjunctive_case16617_leaf_count +
      candle_disjunctive_case16593_leaf_count +
      candle_disjunctive_case16582_leaf_count) ^
   " numerical_cells=" ^
   string_of_int candle_disjunctive_next_batch_total_cells ^
   " components=" ^
   string_of_int (length candle_disjunctive_next_batch_components) ^
   " function0_components=" ^
   string_of_int (length candle_disjunctive_next_batch_components0) ^
   " function1_components=" ^
   string_of_int (length candle_disjunctive_next_batch_components1) ^
   " function0_cells=" ^
   string_of_int (length candle_disjunctive_next_batch_cells0) ^
   " function1_cells=" ^
   string_of_int (length candle_disjunctive_next_batch_cells1) ^
   " token_items=" ^
   string_of_int candle_disjunctive_next_batch_total_tokens ^
   " numerical_programs=2");;

end;;
