(* Mixed-disjunct forest plan for the second authentic sibling batch. *)

needs "candle/cv_compute_analytic_expr_disjunctive_second_sibling_batch.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_forest_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_second_sibling_batch_forest_plan = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_second_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;

let candle_disjunctive_case16482_refined_indices =
  [1;5;9;10;14;21;29;36;39;43;45;50;51;53;59;60;61;62;63;65;66;74;
   80;83;84;91;95;97;145;168;221;230;244;255;269;315;318;325;330;331;
   333;348;352;356;358;360;362;364;367;374;384;389;402;405;408;411;419;
   420;430;439;454;457;466;468;469;472;475;476;478;479;482;485;498;508;
   521;562;564;588;595;613;616;620;635;639;647;651;653;700;716;723;728;
   765;773;791;807;823;857;859;875;879;881;882;883;885;886;893;901;905;
   975;1002;1052;1058;1059;1064;1071;1073;1084;1085;1089;1091;1093;
   1108;1109;1114;1119;1125;1128;1129;1140;1142;1171;1189;1195;1210;
   1212;1252;1282];;
let candle_disjunctive_case16656_refined_indices =
  [378;383;390;391;394;399;431];;
let candle_disjunctive_case16647_refined_indices =
  [400;408;411;482;620;629];;

let candle_disjunctive_second_batch_refinement record indices =
  map
    (fun index ->
      let axis =
        if record = 16482 && (index = 59 || index = 60) then 2 else 1 in
      record,index,1,axis)
    indices;;

let candle_disjunctive_second_batch_split_selected_complete =
  candle_disjunctive_second_batch_refinement
    16482 candle_disjunctive_case16482_refined_indices @
  candle_disjunctive_second_batch_refinement
    16656 candle_disjunctive_case16656_refined_indices @
  candle_disjunctive_second_batch_refinement
    16647 candle_disjunctive_case16647_refined_indices;;

let rec candle_disjunctive_second_batch_distinct = function
  | [] -> true
  | head::tail ->
      not (List.mem head tail) &&
      candle_disjunctive_second_batch_distinct tail;;

let candle_disjunctive_second_batch_split_axis record index selected =
  let rec find = function
    | [] -> None
    | (actual_record,actual_index,actual_selected,axis)::remaining ->
        if actual_record = record && actual_index = index &&
           actual_selected = selected
        then Some axis
        else find remaining in
  find candle_disjunctive_second_batch_split_selected_complete;;

let rec candle_disjunctive_second_batch_shape_build
    record next_leaf domain tree =
  match tree with
  | P_result_pass (_,selected,raw_flag) ->
      if selected < 0 || selected > 1 || raw_flag then
        failwith "second sibling forest plan: pass selection drift";
      let source_leaf = next_leaf in
      (match candle_disjunctive_second_batch_split_axis
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
      if convex_flag then failwith "second sibling forest plan: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left,left_cells,left_glues =
        candle_disjunctive_second_batch_shape_build
          record next_leaf left_domain left in
      let right_shape,after_right,right_cells,right_glues =
        candle_disjunctive_second_batch_shape_build
          record after_left right_domain right in
      Candle_disjunctive_next_batch_node
        (axis,domain,left_shape,right_shape),
      after_right,left_cells + right_cells,1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "second sibling forest plan: monotonicity node"
  | P_result_ref _ ->
      failwith "second sibling forest plan: reference node";;

if length candle_disjunctive_case16482_refined_indices <> 137 ||
   length candle_disjunctive_case16656_refined_indices <> 7 ||
   length candle_disjunctive_case16647_refined_indices <> 6 ||
   not
     (candle_disjunctive_second_batch_distinct
       candle_disjunctive_second_batch_split_selected_complete) then
  failwith "second sibling forest plan: refinement selection drift";;

let candle_disjunctive_case16482_shape,
    candle_disjunctive_case16482_after_leaf,
    candle_disjunctive_case16482_numerical_cells,
    candle_disjunctive_case16482_glue_nodes =
  candle_disjunctive_second_batch_shape_build
    16482 0 candle_disjunctive_case16482_root_domain
    candle_disjunctive_case16482_precision_tree;;
let candle_disjunctive_case16656_shape,
    candle_disjunctive_case16656_after_leaf,
    candle_disjunctive_case16656_numerical_cells,
    candle_disjunctive_case16656_glue_nodes =
  candle_disjunctive_second_batch_shape_build
    16656 0 candle_disjunctive_case16656_root_domain
    candle_disjunctive_case16656_precision_tree;;
let candle_disjunctive_case16647_shape,
    candle_disjunctive_case16647_after_leaf,
    candle_disjunctive_case16647_numerical_cells,
    candle_disjunctive_case16647_glue_nodes =
  candle_disjunctive_second_batch_shape_build
    16647 0 candle_disjunctive_case16647_root_domain
    candle_disjunctive_case16647_precision_tree;;

let candle_disjunctive_case16482_skeleton,
    candle_disjunctive_case16482_after_component,
    candle_disjunctive_case16482_components =
  candle_disjunctive_next_batch_skeletonize
    16482 0 candle_disjunctive_case16482_shape;;
let candle_disjunctive_case16656_skeleton,
    candle_disjunctive_case16656_after_component,
    candle_disjunctive_case16656_components =
  candle_disjunctive_next_batch_skeletonize
    16656 candle_disjunctive_case16482_after_component
    candle_disjunctive_case16656_shape;;
let candle_disjunctive_case16647_skeleton,
    candle_disjunctive_case16647_after_component,
    candle_disjunctive_case16647_components =
  candle_disjunctive_next_batch_skeletonize
    16647 candle_disjunctive_case16656_after_component
    candle_disjunctive_case16647_shape;;

let candle_disjunctive_second_batch_components =
  candle_disjunctive_case16482_components @
  candle_disjunctive_case16656_components @
  candle_disjunctive_case16647_components;;
let candle_disjunctive_second_batch_components0 =
  List.filter
    (fun component -> component.next_batch_component_selected = 0)
    candle_disjunctive_second_batch_components;;
let candle_disjunctive_second_batch_components1 =
  List.filter
    (fun component -> component.next_batch_component_selected = 1)
    candle_disjunctive_second_batch_components;;
let candle_disjunctive_second_batch_cells0,
    candle_disjunctive_second_batch_tokens0,
    candle_disjunctive_second_batch_expected_stack0 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_second_batch_components0;;
let candle_disjunctive_second_batch_cells1,
    candle_disjunctive_second_batch_tokens1,
    candle_disjunctive_second_batch_expected_stack1 =
  candle_disjunctive_next_batch_forest
    candle_disjunctive_second_batch_components1;;

let candle_disjunctive_second_batch_total_cells =
  candle_disjunctive_case16482_numerical_cells +
  candle_disjunctive_case16656_numerical_cells +
  candle_disjunctive_case16647_numerical_cells;;
let candle_disjunctive_second_batch_total_tokens =
  length candle_disjunctive_second_batch_tokens0 +
  length candle_disjunctive_second_batch_tokens1;;

if candle_disjunctive_case16482_after_leaf <>
     candle_disjunctive_case16482_leaf_count ||
   candle_disjunctive_case16656_after_leaf <>
     candle_disjunctive_case16656_leaf_count ||
   candle_disjunctive_case16647_after_leaf <>
     candle_disjunctive_case16647_leaf_count ||
   candle_disjunctive_second_batch_total_cells <> 4215 ||
   candle_disjunctive_case16647_after_component <>
     length candle_disjunctive_second_batch_components ||
   length candle_disjunctive_second_batch_cells0 +
     length candle_disjunctive_second_batch_cells1 <>
     candle_disjunctive_second_batch_total_cells ||
   candle_disjunctive_second_batch_total_tokens <>
     2 * candle_disjunctive_second_batch_total_cells -
     length candle_disjunctive_second_batch_components then
  failwith "second sibling forest plan: final accounting drift";;

print_endline
  ("CANDLE_CV_SECOND_SIBLING_BATCH_FOREST_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " source_leaves=" ^
   string_of_int
     (candle_disjunctive_case16482_leaf_count +
      candle_disjunctive_case16656_leaf_count +
      candle_disjunctive_case16647_leaf_count) ^
   " numerical_cells=" ^
   string_of_int candle_disjunctive_second_batch_total_cells ^
   " components=" ^
   string_of_int (length candle_disjunctive_second_batch_components) ^
   " function0_components=" ^
   string_of_int (length candle_disjunctive_second_batch_components0) ^
   " function1_components=" ^
   string_of_int (length candle_disjunctive_second_batch_components1) ^
   " function0_cells=" ^
   string_of_int (length candle_disjunctive_second_batch_cells0) ^
   " function1_cells=" ^
   string_of_int (length candle_disjunctive_second_batch_cells1) ^
   " token_items=" ^
   string_of_int candle_disjunctive_second_batch_total_tokens ^
   " numerical_programs=2");;

end;;
