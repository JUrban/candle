(* ========================================================================== *)
(* Stable-source fixed-nonlinear adapter for genuine action-296 forests.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The authenticated expression and compiled     *)
(* program are reused across the complete forest.  Whole-box and center       *)
(* square-root certificates remain checked job data.  One reflected batch    *)
(* verdict yields every final-cell theorem before the exact Flyspeck trees    *)
(* are reconstructed with their existing kernel glue.                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_fixed_nonlinear_forest_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_prove.ml";;

module Candle_cv_action296_fixed_nonlinear_variable_forest_prove = struct

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_action296_forest_plan;;
open Candle_cv_action296_fixed_nonlinear_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_prove;;

type candle_action296_fixed_nonlinear_variable_root = {
  fixed_nonlinear_variable_root_index : int;
  fixed_nonlinear_variable_root_parent : thm;
  fixed_nonlinear_variable_root_tree : candle_action296_forest_tree;
  fixed_nonlinear_variable_root_domains : thm list;
  fixed_nonlinear_variable_root_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

type candle_action296_fixed_nonlinear_variable_forest_result = {
  fixed_nonlinear_variable_forest_result_original_roots : int;
  fixed_nonlinear_variable_forest_result_final_cells : int;
  fixed_nonlinear_variable_forest_result_theorems : (int * thm) list;
  fixed_nonlinear_variable_forest_result_digest : string;
};;

let candle_action296_fixed_nonlinear_variable_forest_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-nonlinear-variable-forest" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fixed_nonlinear_variable_forest_point_plan =
  candle_q_dim_taylor_model_point_plan_six candle_action296_plan_prepared;;

let candle_action296_fixed_nonlinear_variable_forest_box_intervals lower upper =
  candle_q_box_rational_program_intervals_six
    candle_action296_fixed_nonlinear_variable_forest_point_plan.
      point_plan_programs
    lower upper;;

let candle_action296_fixed_nonlinear_variable_forest_cell
    box_intervals domain =
  let lower,upper = candle_action296_leaf_grouping_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_action296_fixed_nonlinear_variable_forest_point_plan
      lower upper in
  {variable_batch_box_intervals = box_intervals;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_action296_fixed_nonlinear_variable_forest_prepare_root
    (index,plan_data) =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let box_intervals =
    candle_action296_fixed_nonlinear_variable_forest_box_intervals
      lower upper in
  let tree = candle_action296_forest_build_tree parent plan_data in
  let domains = candle_action296_forest_tree_domains tree in
  let cells =
    map
      (candle_action296_fixed_nonlinear_variable_forest_cell box_intervals)
      domains in
  {fixed_nonlinear_variable_root_index = index;
   fixed_nonlinear_variable_root_parent = parent;
   fixed_nonlinear_variable_root_tree = tree;
   fixed_nonlinear_variable_root_domains = domains;
   fixed_nonlinear_variable_root_cells = cells};;

let rec candle_action296_fixed_nonlinear_variable_forest_take count items =
  if count = 0 then [],items else
  match items with
  | head :: tail ->
      let selected,remaining =
        candle_action296_fixed_nonlinear_variable_forest_take
          (count - 1) tail in
      head :: selected,remaining
  | [] ->
      failwith "fixed nonlinear variable forest: result underflow";;

let rec candle_action296_fixed_nonlinear_variable_forest_map3 operation
    left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head :: left_tail,middle_head :: middle_tail,
      right_head :: right_tail ->
      operation left_head middle_head right_head ::
      candle_action296_fixed_nonlinear_variable_forest_map3 operation
        left_tail middle_tail right_tail
  | _ -> failwith "fixed nonlinear variable forest: map3 shape";;

let candle_action296_fixed_nonlinear_variable_forest_live
    source cell domain =
  let expected = cell.variable_batch_stable_cell in
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_fixed_nonlinear_forest_aconv_lists
             lower expected.stable_batch_lower &&
           candle_action296_fixed_nonlinear_forest_aconv_lists
             upper expected.stable_batch_upper) then
        failwith "fixed nonlinear variable forest: unexpected handoff box";
      source)
    domain;;

let candle_action296_fixed_nonlinear_variable_forest_finish_root
    prepared sources =
  let live =
    candle_action296_fixed_nonlinear_variable_forest_map3
      candle_action296_fixed_nonlinear_variable_forest_live
      sources
      prepared.fixed_nonlinear_variable_root_cells
      prepared.fixed_nonlinear_variable_root_domains in
  let theorem,remaining =
    candle_action296_fixed_nonlinear_forest_glue
      prepared.fixed_nonlinear_variable_root_tree live in
  if remaining <> [] ||
     not
       (candle_action296_fixed_nonlinear_forest_validate_result
         prepared.fixed_nonlinear_variable_root_index
         prepared.fixed_nonlinear_variable_root_parent theorem) then
    failwith
      ("fixed nonlinear variable forest: invalid root " ^
       string_of_int prepared.fixed_nonlinear_variable_root_index);
  prepared.fixed_nonlinear_variable_root_index,theorem;;

let candle_action296_fixed_nonlinear_variable_forest_prove
    label roots expected_final_cells expected_digest =
  if roots = [] ||
     not
       (candle_action296_fixed_nonlinear_forest_strict_roots (-1) roots) then
    failwith "fixed nonlinear variable forest: invalid root plan";
  let axioms_before = axioms () in
  candle_action296_fixed_nonlinear_variable_forest_marker
    "certificate-data" "begin";
  let prepared_roots =
    map candle_action296_fixed_nonlinear_variable_forest_prepare_root roots in
  let cells =
    List.flatten
      (map
        (fun root -> root.fixed_nonlinear_variable_root_cells)
        prepared_roots) in
  candle_action296_fixed_nonlinear_variable_forest_marker
    "certificate-data" "end";
  if length cells <> expected_final_cells then
    failwith "fixed nonlinear variable forest: final-cell count drift";
  candle_action296_fixed_nonlinear_variable_forest_marker
    "one-verdict-proof" "begin";
  let batch =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_prove_six
      candle_action296_plan_prepared cells in
  candle_action296_fixed_nonlinear_variable_forest_marker
    "one-verdict-proof" "end";
  candle_action296_fixed_nonlinear_variable_forest_marker
    "source-theorem-extraction" "begin";
  let sources =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_sources_six
      batch in
  candle_action296_fixed_nonlinear_variable_forest_marker
    "source-theorem-extraction" "end";
  if length sources <> expected_final_cells then
    failwith "fixed nonlinear variable forest: source count drift";
  candle_action296_fixed_nonlinear_variable_forest_marker
    "live-handoff-and-glue" "begin";
  let rec finish remaining_sources = function
    | [] -> [],remaining_sources
    | root :: rest ->
        let count = length root.fixed_nonlinear_variable_root_cells in
        let selected,after_root =
          candle_action296_fixed_nonlinear_variable_forest_take
            count remaining_sources in
        let theorem =
          candle_action296_fixed_nonlinear_variable_forest_finish_root
            root selected in
        let completed,remaining = finish after_root rest in
        theorem :: completed,remaining in
  let root_results,remaining = finish sources prepared_roots in
  candle_action296_fixed_nonlinear_variable_forest_marker
    "live-handoff-and-glue" "end";
  if remaining <> [] then
    failwith "fixed nonlinear variable forest: unused sources";
  let digest =
    Digest.to_hex
      (Digest.string
        (String.concat "\n"
          (map (fun (_,theorem) -> string_of_thm theorem) root_results))) in
  let axioms_after = axioms () in
  let digest_matches =
    match expected_digest with
    | None -> true
    | Some expected -> digest = expected in
  if length root_results <> length roots ||
     not digest_matches ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith
      ("fixed nonlinear variable forest: final validation failed for " ^
       label);
  {fixed_nonlinear_variable_forest_result_original_roots = length roots;
   fixed_nonlinear_variable_forest_result_final_cells = length cells;
   fixed_nonlinear_variable_forest_result_theorems = root_results;
   fixed_nonlinear_variable_forest_result_digest = digest};;

end;;
