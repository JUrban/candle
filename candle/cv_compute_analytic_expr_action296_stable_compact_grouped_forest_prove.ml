(* ========================================================================== *)
(* Stable-source action-296 groups with one compact topology verdict/root.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Stable numerical batches are unchanged.      *)
(* Instead of reconstructing one theorem per final cell and recursively      *)
(* gluing it, this adapter checks each untrusted exact split tree as data and *)
(* applies the general compact fixed-algebraic soundness theorem once.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_stable_grouped_forest_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_prove.ml";;

module Candle_cv_action296_stable_compact_grouped_forest_prove = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_prove;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_action296_adaptive_forest_prove;;
open Candle_cv_action296_bounded_grouped_forest_prove;;
open Candle_cv_action296_stable_grouped_forest_prove;;

type candle_action296_stable_compact_logical_root_six = {
  stable_compact_root_index : int;
  stable_compact_root_parent : thm;
  stable_compact_root_tree : term;
  stable_compact_root_lower : term list;
  stable_compact_root_upper : term list;
};;

let candle_action296_stable_compact_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stable-compact-grouped-forest" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_stable_compact_string_of_bool value =
  if value then "true" else "false";;

let candle_action296_stable_compact_profile phase operation =
  let _ = candle_action296_stable_compact_marker phase "begin" in
  try
    let result = operation () in
    let _ = candle_action296_stable_compact_marker phase "end" in
    result
  with Failure message ->
    let _ = candle_action296_stable_compact_marker phase "end" in
    failwith message;;

let candle_action296_stable_compact_leaf_term center boxes =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_leaf`,[center;boxes]);;

let candle_action296_stable_compact_node_term axis boxes left right =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_node`,
     [axis;boxes;left;right]);;

let candle_action296_stable_compact_domain_matches left right =
  let left_lower,left_upper =
    candle_action296_leaf_grouping_domain_bounds left and
      right_lower,right_upper =
        candle_action296_leaf_grouping_domain_bounds right in
  candle_action296_forest_aconv_lists left_lower right_lower &&
  candle_action296_forest_aconv_lists left_upper right_upper;;

let rec candle_action296_stable_compact_logical_tree
    domain prepared_cells = function
  | Candle_action296_forest_tree_leaf stored_domain ->
      if not
          (candle_action296_stable_compact_domain_matches
            domain stored_domain) then
        failwith "action296 stable compact: leaf domain mismatch";
      (match prepared_cells with
       | [] -> failwith "action296 stable compact: missing prepared cell"
       | prepared :: remaining ->
           let lower,upper =
             candle_action296_leaf_grouping_domain_bounds domain in
           let expected_boxes =
             candle_poly_fixture_q_boxes lower upper in
           let center,boxes =
             dest_pair prepared.stable_batch_materialized_job_term in
           if not
               (aconv boxes prepared.stable_batch_boxes_term &&
                aconv boxes expected_boxes) then
             failwith "action296 stable compact: leaf job mismatch";
           candle_action296_stable_compact_leaf_term
             center boxes,remaining)
  | Candle_action296_forest_tree_split (axis,left,right) ->
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain in
      let left_tree,after_left =
        candle_action296_stable_compact_logical_tree
          left_domain prepared_cells left in
      let right_tree,remaining =
        candle_action296_stable_compact_logical_tree
          right_domain after_left right in
      let lower,upper =
        candle_action296_leaf_grouping_domain_bounds domain in
      let boxes = candle_poly_fixture_q_boxes lower upper in
      candle_action296_stable_compact_node_term
        (mk_small_numeral axis) boxes left_tree right_tree,
      remaining;;

let rec candle_action296_stable_compact_logical_roots
    prepared_cells = function
  | [] ->
      if prepared_cells = [] then []
      else failwith "action296 stable compact: trailing prepared cells"
  | root :: remaining_roots ->
      let lower,upper =
        candle_action296_leaf_grouping_domain_bounds
          root.stable_group_root_parent in
      let tree,remaining_cells =
        candle_action296_stable_compact_logical_tree
          root.stable_group_root_parent prepared_cells
          root.stable_group_root_tree in
      {stable_compact_root_index = root.stable_group_root_index;
       stable_compact_root_parent = root.stable_group_root_parent;
       stable_compact_root_tree = tree;
       stable_compact_root_lower = lower;
       stable_compact_root_upper = upper} ::
      candle_action296_stable_compact_logical_roots
        remaining_cells remaining_roots;;

let candle_action296_stable_compact_append_function =
  `APPEND:
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list->
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list->
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list`;;

let candle_action296_stable_compact_root_live function_term source root =
  candle_reflected_nl_source_pass_with
    function_term
    (fun lower upper ->
      if not
          (candle_action296_forest_aconv_lists
             lower root.stable_compact_root_lower &&
           candle_action296_forest_aconv_lists
             upper root.stable_compact_root_upper) then
        failwith "action296 stable compact: unexpected root handoff box";
      source)
    root.stable_compact_root_parent;;

let rec candle_action296_stable_compact_project_roots
    box_expression valid patch_denotation source_theorem function_term
    remaining_jobs remaining_accept = function
  | [] -> [],remaining_jobs,remaining_accept
  | root :: remaining_roots ->
      let root_label = string_of_int root.stable_compact_root_index in
      let _ =
        candle_action296_stable_compact_marker
          ("compact-root-" ^ root_label) "begin" in
      let jobs_call =
        mk_comb
          (`candle_q_dim_taylor_model_tree_jobs`,
           root.stable_compact_root_tree) in
      let jobs_expansion =
        REWRITE_CONV
          [candle_q_dim_taylor_model_tree_jobs_def;APPEND]
          jobs_call in
      let tree_jobs = rand (concl jobs_expansion) in
      let tree_items = dest_list tree_jobs and
          remaining_items = dest_list remaining_jobs in
      let tree_count = length tree_items in
      if tree_count = 0 || tree_count > length remaining_items ||
         not
           (candle_action296_forest_aconv_lists
             tree_items (fst (chop_list tree_count remaining_items))) then
        failwith "action296 stable compact: non-prefix tree jobs";
      let _,suffix_items = chop_list tree_count remaining_items in
      let suffix_jobs =
        mk_list (suffix_items,type_of (hd remaining_items)) in
      let append_call =
        list_mk_comb
          (candle_action296_stable_compact_append_function,
           [tree_jobs;suffix_jobs]) in
      let append_expansion = REWRITE_CONV [APPEND] append_call in
      if hyp append_expansion <> [] ||
         not (aconv (rand (concl append_expansion)) remaining_jobs) then
        failwith "action296 stable compact: append mismatch";
      let split_accept =
        REWRITE_RULE
          [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_append]
          (REWRITE_RULE [SYM append_expansion] remaining_accept) in
      let tree_accept,suffix_accept =
        if suffix_items = [] then begin
          if remaining_roots <> [] ||
             not (aconv tree_jobs remaining_jobs) then
            failwith "action296 stable compact: malformed terminal tree";
          remaining_accept,remaining_accept
        end else
          CONJ_PAIR split_accept in
      candle_q_dim_taylor_model_tree_compact_prove_profile :=
        (fun event ->
          print_endline
            ("CANDLE_STABLE_COMPACT_STEP root=" ^ root_label ^
             " event=" ^ event));
      let cell =
        candle_q_dim_taylor_model_fixed_algebraic_tree_compact_cell_six
          box_expression valid tree_jobs tree_accept
          root.stable_compact_root_tree in
      let source =
        REWRITE_RULE
          [m_cell_pass;candle_q_dim_taylor_model_tree_root_boxes_def;
           SYM patch_denotation;source_theorem]
          cell in
      let live =
        candle_action296_stable_compact_root_live
          function_term source root in
      let _ =
        candle_action296_stable_compact_marker
          ("compact-root-" ^ root_label) "end" in
      let projected,final_jobs,final_accept =
        candle_action296_stable_compact_project_roots
          box_expression valid patch_denotation source_theorem function_term
          suffix_jobs suffix_accept remaining_roots in
      (root.stable_compact_root_index,live) :: projected,
      final_jobs,final_accept;;

let candle_action296_stable_compact_project_group result roots =
  let materialized_expansion =
    REWRITE_CONV
      [candle_q_dim_taylor_model_stable_jobs_materialize_def]
      result.stable_batch_materialized_jobs_term in
  let jobs = rand (concl materialized_expansion) in
  let accept =
    REWRITE_RULE [materialized_expansion]
      result.stable_batch_accept_theorem in
  let logical_roots =
    candle_action296_stable_compact_logical_roots
      result.stable_batch_prepared_cells roots in
  let box_expression =
    candle_q_dim_taylor_model_stable_batch_patch_expression
      result.stable_batch_box_intervals_term
      result.stable_batch_prepared_source.expression_term in
  let valid =
    MATCH_MP
      (SPECL
        [result.stable_batch_prepared_source.expression_term;
         result.stable_batch_box_intervals_term;`6`]
        candle_analytic_patch_sqrt_certificates_valid_dim)
      result.stable_batch_prepared_source.valid_theorem in
  let patch_denotation =
    INST_TYPE
      [`:6`,`:N`]
      (SPECL
        [result.stable_batch_prepared_source.expression_term;
         result.stable_batch_box_intervals_term]
        candle_analytic_patch_sqrt_certificates_denote_dim) in
  let projected,remaining_jobs,_ =
    candle_action296_stable_compact_project_roots
      box_expression valid patch_denotation
      result.stable_batch_prepared_source.source_theorem
      result.stable_batch_prepared_source.function_term
      jobs accept logical_roots in
  if dest_list remaining_jobs <> [] then
    failwith "action296 stable compact: unconsumed jobs";
  projected;;

let candle_action296_stable_compact_prove_attempt
    attempt point_plan roots =
  if roots = [] then failwith "action296 stable compact: empty attempt";
  let parents =
    map
      (fun (index,_) ->
        index,List.nth !candle_action296_leaf_grouping_leaves index)
      roots in
  let phase suffix =
    candle_action296_stable_group_phase attempt roots suffix in
  let box_intervals =
    candle_action296_stable_compact_profile
      (phase "whole-box-certificate-data")
      (fun () ->
        let lower,upper =
          candle_action296_leaf_grouping_envelope (map snd parents) in
        candle_action296_stable_group_box_intervals
          point_plan lower upper) in
  let grouped_roots,cells =
    candle_action296_stable_compact_profile (phase "final-cell-data")
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
    candle_action296_stable_compact_profile (phase "stable-batch-proof")
      (fun () ->
        candle_q_dim_taylor_model_stable_batch_prove_six
          candle_action296_plan_prepared box_intervals cells) in
  let results =
    candle_action296_stable_compact_profile (phase "compact-root-handoff")
      (fun () ->
        candle_action296_stable_compact_project_group
          aggregate grouped_roots) in
  if not (candle_action296_forest_validate_results roots results parents) then
    failwith "action296 stable compact: group result validation";
  results,length cells;;

let candle_action296_stable_compact_prove_sizes point_plan sizes roots =
  let _,outcome =
    List.fold_left
      (fun (attempt,accumulated) group ->
        let results,cells =
          candle_action296_stable_compact_prove_attempt
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

let candle_action296_stable_compact_grouped_forest_prove_sizes
    label sizes roots expected_final_cells expected_digest =
  if roots = [] ||
     not (candle_action296_forest_strict_roots (-1) roots) then
    failwith "action296 stable compact: invalid root plan";
  let axioms_before = axioms () in
  let point_plan = candle_action296_forest_point_plan in
  let _ = candle_action296_stable_compact_marker "compact-forest" "begin" in
  let outcome =
    candle_action296_stable_compact_prove_sizes point_plan sizes roots in
  let _ = candle_action296_stable_compact_marker "compact-forest" "end" in
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
  let results_valid =
    candle_action296_forest_validate_results
      roots outcome.stable_group_results parents and
      final_cells_match =
        outcome.stable_group_final_cells = expected_final_cells and
      axiom_count_matches =
        length axioms_after = length axioms_before and
      axioms_preserved =
        List.for_all
          (fun theorem -> List.mem theorem axioms_before)
          axioms_after in
  let _ =
    print_endline
      ("CANDLE_CV_ACTION296_STABLE_COMPACT_VALIDATION" ^
       " results_valid=" ^
         candle_action296_stable_compact_string_of_bool results_valid ^
       " final_cells_match=" ^
         candle_action296_stable_compact_string_of_bool final_cells_match ^
       " digest_matches=" ^
         candle_action296_stable_compact_string_of_bool digest_matches ^
       " axioms_preserved=" ^
         candle_action296_stable_compact_string_of_bool
           (axiom_count_matches && axioms_preserved) ^
       " theorem_digest=" ^ digest) in
  if not results_valid || not final_cells_match || not digest_matches ||
     not axiom_count_matches || not axioms_preserved then
    failwith
      ("action296 stable compact: final validation failed for " ^ label);
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
