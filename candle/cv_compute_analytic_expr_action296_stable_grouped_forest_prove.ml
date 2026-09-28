(* ========================================================================== *)
(* Stable-source grouped proof adapter for the complete action-296 forest.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Source authentication and point-plan          *)
(* compilation are shared globally.  Each bounded root group supplies only   *)
(* its whole-box and center square-root certificates and exact final boxes.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_bounded_grouped_forest_prove.ml";;
needs "candle/cv_compute_analytic_expr_stable_batch_prove.ml";;

module Candle_cv_action296_stable_grouped_forest_prove = struct

open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_action296_adaptive_forest_prove;;
open Candle_cv_action296_bounded_grouped_forest_prove;;

type candle_action296_stable_group_root_six = {
  stable_group_root_index : int;
  stable_group_root_parent : thm;
  stable_group_root_tree : candle_action296_forest_tree;
  stable_group_root_domains : thm list;
  stable_group_root_cells :
    candle_q_dim_taylor_model_stable_batch_cell_six list;
};;

type candle_action296_stable_group_outcome = {
  stable_group_results : (int * thm) list;
  stable_group_final_cells : int;
  stable_group_attempts : int;
  stable_group_sizes : int list;
};;

type candle_action296_stable_group_result = {
  stable_group_forest_result : candle_action296_forest_result;
  stable_group_attempts_total : int;
  stable_group_successful_sizes : int list;
};;

let candle_action296_stable_group_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stable-grouped-forest-proof" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_stable_group_profile phase operation =
  let _ = candle_action296_stable_group_marker phase "begin" in
  try
    let result = operation () in
    let _ = candle_action296_stable_group_marker phase "end" in
    result
  with Failure message ->
    let _ = candle_action296_stable_group_marker phase "end" in
    failwith message;;

let candle_action296_stable_group_current_phase = ref "setup";;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      if event =
           "stable-certified-taylor-batch-preparation-begin" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-proof-input-preparation") "begin"
      else if event =
           "stable-certified-taylor-batch-preparation-end" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-proof-input-preparation") "end"
      else if event =
           "stable-certified-taylor-batch-compute-begin" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-kernel-compute") "begin"
      else if event =
           "stable-certified-taylor-batch-compute-end" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-kernel-compute") "end"
      else if event =
           "stable-certified-taylor-batch-handoff-begin" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-verdict-handoff") "begin"
      else if event =
           "stable-certified-taylor-batch-handoff-end" then
        candle_action296_stable_group_marker
          (!candle_action296_stable_group_current_phase ^
           "-verdict-handoff") "end"
      else ());;

let candle_action296_stable_group_variables =
  candle_poly_vector_components
    candle_action296_plan_prepared.vector_term 6;;

let candle_action296_stable_group_box_intervals lower upper =
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  let intervals =
    candle_analytic_collect_sqrt_intervals
      (candle_q_box_sqrt_callback
        candle_action296_stable_group_variables bounds)
      candle_action296_stable_group_variables
      candle_action296_plan_prepared.source_term in
  if length intervals <> 7 then
    failwith "action296 stable grouping: square-root slot count drift";
  intervals;;

let candle_action296_stable_group_cell point_plan domain =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  if length center_intervals <> 7 then
    failwith "action296 stable grouping: center slot count drift";
  {stable_batch_center_intervals = center_intervals;
   stable_batch_lower = lower;
   stable_batch_upper = upper};;

let candle_action296_stable_group_root point_plan (index,plan_data) =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let tree = candle_action296_forest_build_tree parent plan_data in
  let domains = candle_action296_forest_tree_domains tree in
  {
    stable_group_root_index = index;
    stable_group_root_parent = parent;
    stable_group_root_tree = tree;
    stable_group_root_domains = domains;
    stable_group_root_cells =
      map (candle_action296_stable_group_cell point_plan) domains;
  };;

let candle_action296_stable_group_live cell source domain =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_forest_aconv_lists
             lower cell.stable_batch_lower &&
           candle_action296_forest_aconv_lists
             upper cell.stable_batch_upper) then
        failwith "action296 stable grouping: unexpected handoff box";
      source)
    domain;;

let rec candle_action296_stable_group_consume_sources sources roots =
  match roots with
  | [] ->
      if sources = [] then []
      else failwith "action296 stable grouping: trailing source theorems"
  | root :: remaining_roots ->
      let count = length root.stable_group_root_domains in
      let selected,remaining_sources =
        candle_action296_bounded_group_take count sources in
      if length selected <> count then
        failwith "action296 stable grouping: missing source theorems";
      let live =
        candle_action296_forest_map3
          candle_action296_stable_group_live
          root.stable_group_root_cells selected
          root.stable_group_root_domains in
      let theorem,trailing =
        candle_action296_forest_glue root.stable_group_root_tree live in
      if trailing <> [] then
        failwith "action296 stable grouping: trailing live leaves";
      (root.stable_group_root_index,theorem) ::
        candle_action296_stable_group_consume_sources
          remaining_sources remaining_roots;;

let candle_action296_stable_group_phase attempt roots suffix =
  let first = fst (hd roots) and last = fst (hd (rev roots)) in
  "attempt-" ^ string_of_int attempt ^ "-roots-" ^
  string_of_int first ^ "-" ^ string_of_int last ^ "-" ^ suffix;;

let candle_action296_stable_group_prove_attempt
    attempt point_plan roots =
  if roots = [] then failwith "action296 stable grouping: empty attempt";
  let parents =
    map
      (fun (index,_) ->
        index,List.nth !candle_action296_leaf_grouping_leaves index)
      roots in
  let phase suffix =
    candle_action296_stable_group_phase attempt roots suffix in
  let box_intervals =
    candle_action296_stable_group_profile
      (phase "whole-box-certificate-data")
      (fun () ->
        let lower,upper =
          candle_action296_leaf_grouping_envelope (map snd parents) in
        candle_action296_stable_group_box_intervals lower upper) in
  let grouped_roots,cells =
    candle_action296_stable_group_profile (phase "final-cell-data")
      (fun () ->
        let grouped_roots =
          map (candle_action296_stable_group_root point_plan) roots in
        let cells =
          List.flatten
            (map
              (fun root -> root.stable_group_root_cells)
              grouped_roots) in
        grouped_roots,cells) in
  candle_action296_stable_group_current_phase :=
    candle_action296_stable_group_phase attempt roots "stable-batch";
  let aggregate =
    candle_action296_stable_group_profile (phase "stable-batch-proof")
      (fun () ->
        candle_q_dim_taylor_model_stable_batch_prove_six
          candle_action296_plan_prepared box_intervals cells) in
  let sources =
    candle_action296_stable_group_profile (phase "source-extraction")
      (fun () ->
        candle_q_dim_taylor_model_stable_batch_cell_sources_six
          aggregate) in
  let results =
    candle_action296_stable_group_profile (phase "live-handoff-and-glue")
      (fun () ->
        candle_action296_stable_group_consume_sources
          sources grouped_roots) in
  if not (candle_action296_forest_validate_results roots results parents) then
    failwith "action296 stable grouping: group result validation";
  results,length cells;;

let candle_action296_stable_group_append left right =
  {
    stable_group_results =
      left.stable_group_results @ right.stable_group_results;
    stable_group_final_cells =
      left.stable_group_final_cells + right.stable_group_final_cells;
    stable_group_attempts =
      left.stable_group_attempts + right.stable_group_attempts;
    stable_group_sizes =
      left.stable_group_sizes @ right.stable_group_sizes;
  };;

let candle_action296_stable_group_prove_sizes point_plan sizes roots =
  let _,outcome =
    List.fold_left
      (fun (attempt,accumulated) group ->
        let results,cells =
          candle_action296_stable_group_prove_attempt
            attempt point_plan group in
        attempt + 1,
        candle_action296_stable_group_append accumulated
          {stable_group_results = results;
           stable_group_final_cells = cells;
           stable_group_attempts = 1;
           stable_group_sizes = [length group]})
      (1,
       {stable_group_results = [];
        stable_group_final_cells = 0;
        stable_group_attempts = 0;
        stable_group_sizes = []})
      (candle_action296_bounded_group_partition_sizes sizes roots) in
  outcome;;

let candle_action296_stable_grouped_forest_prove_sizes
    label sizes roots expected_final_cells expected_digest =
  if roots = [] ||
     not (candle_action296_forest_strict_roots (-1) roots) then
    failwith "action296 stable grouping: invalid root plan";
  let axioms_before = axioms () in
  let point_plan =
    candle_action296_stable_group_profile
      "shared-point-plan-reuse"
      (fun () -> candle_action296_forest_point_plan) in
  let _ = candle_action296_stable_group_marker "bounded-forest" "begin" in
  let outcome =
    candle_action296_stable_group_prove_sizes point_plan sizes roots in
  let _ = candle_action296_stable_group_marker "bounded-forest" "end" in
  let digest =
    Digest.to_hex
      (Digest.string
        (String.concat "\n"
          (map
            (fun (_,theorem) -> string_of_thm theorem)
            outcome.stable_group_results))) in
  let digest_matches =
    match expected_digest with
    | None -> true
    | Some expected -> digest = expected in
  let parents =
    map
      (fun (index,_) ->
        index,List.nth !candle_action296_leaf_grouping_leaves index)
      roots in
  let axioms_after = axioms () in
  if not
       (candle_action296_forest_validate_results
         roots outcome.stable_group_results parents) ||
     outcome.stable_group_final_cells <> expected_final_cells ||
     not digest_matches ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith
      ("action296 stable grouping: final validation failed for " ^ label);
  {
    stable_group_forest_result = {
      forest_result_original_roots = length roots;
      forest_result_final_cells = outcome.stable_group_final_cells;
      forest_result_theorems = outcome.stable_group_results;
      forest_result_digest = digest;
    };
    stable_group_attempts_total = outcome.stable_group_attempts;
    stable_group_successful_sizes = outcome.stable_group_sizes;
  };;

end;;
