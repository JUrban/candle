(* ========================================================================== *)
(* Data-driven proof adapter for genuine action-296 adaptive leaf forests.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Forest plans are untrusted ordinary data.     *)
(* Every selected final cell is recomputed by the reflected aggregate proof  *)
(* adapter, transported to its exact Flyspeck box, and glued through kernel  *)
(* theorems before an original-root theorem is returned.                      *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_depth2_scan_algebraic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

module Candle_cv_action296_adaptive_forest_prove = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

type candle_action296_forest_plan =
  | Candle_action296_forest_leaf
  | Candle_action296_forest_split of
      int * candle_action296_forest_plan * candle_action296_forest_plan;;

type candle_action296_forest_tree =
  | Candle_action296_forest_tree_leaf of thm
  | Candle_action296_forest_tree_split of
      int * candle_action296_forest_tree * candle_action296_forest_tree;;

type candle_action296_forest_prepared_six = {
  forest_prepared_index : int;
  forest_prepared_parent : thm;
  forest_prepared_plan_data : candle_action296_forest_plan;
  forest_prepared_source : candle_q_dim_analytic_jet_prepared_six;
};;

type candle_action296_forest_planned_six = {
  forest_planned_index : int;
  forest_planned_parent : thm;
  forest_planned_plan_data : candle_action296_forest_plan;
  forest_planned_source : candle_q_dim_analytic_jet_prepared_six;
  forest_planned_point_plan : candle_q_dim_taylor_model_point_plan_six;
};;

type candle_action296_forest_group_six = {
  forest_group_index : int;
  forest_group_parent : thm;
  forest_group_prepared : candle_q_dim_analytic_jet_prepared_six;
  forest_group_tree : candle_action296_forest_tree;
  forest_group_domains : thm list;
  forest_group_cells :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list;
};;

type candle_action296_forest_result = {
  forest_result_original_roots : int;
  forest_result_final_cells : int;
  forest_result_theorems : (int * thm) list;
  forest_result_digest : string;
};;

let candle_action296_forest_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-adaptive-forest-proof" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let rec candle_action296_forest_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_forest_aconv_lists left_tail right_tail
  | _ -> false;;

let rec candle_action296_forest_map2 action left right =
  match left,right with
  | [],[] -> []
  | left_head :: left_tail,right_head :: right_tail ->
      action left_head right_head ::
      candle_action296_forest_map2 action left_tail right_tail
  | _ -> failwith "action296 adaptive forest: map2 shape";;

let rec candle_action296_forest_map3 action left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head :: left_tail,middle_head :: middle_tail,
    right_head :: right_tail ->
      action left_head middle_head right_head ::
      candle_action296_forest_map3 action left_tail middle_tail right_tail
  | _ -> failwith "action296 adaptive forest: map3 shape";;

let rec candle_action296_forest_strict_roots previous = function
  | [] -> true
  | (index,_) :: remaining ->
      index > previous && index >= 0 && index < 1061 &&
      candle_action296_forest_strict_roots index remaining;;

let rec candle_action296_forest_build_tree domain = function
  | Candle_action296_forest_leaf ->
      Candle_action296_forest_tree_leaf domain
  | Candle_action296_forest_split (axis,left_plan,right_plan) ->
      if axis < 1 || axis > 6 then
        failwith "action296 adaptive forest: split axis out of range";
      let left,right =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain in
      Candle_action296_forest_tree_split
        (axis,
         candle_action296_forest_build_tree left left_plan,
         candle_action296_forest_build_tree right right_plan);;

let rec candle_action296_forest_tree_domains = function
  | Candle_action296_forest_tree_leaf domain -> [domain]
  | Candle_action296_forest_tree_split (_,left,right) ->
      candle_action296_forest_tree_domains left @
      candle_action296_forest_tree_domains right;;

let candle_action296_forest_cell case =
  {
    fixed_algebraic_batch_center_variant =
      case.adaptive_grouping_center_variant;
    fixed_algebraic_batch_lower = case.adaptive_grouping_lower;
    fixed_algebraic_batch_upper = case.adaptive_grouping_upper;
  };;

let candle_action296_forest_live cell source domain =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_forest_aconv_lists
             lower cell.fixed_algebraic_batch_lower &&
           candle_action296_forest_aconv_lists
             upper cell.fixed_algebraic_batch_upper) then
        failwith "action296 adaptive forest: unexpected handoff box";
      source)
    domain;;

let rec candle_action296_forest_glue tree live =
  match tree with
  | Candle_action296_forest_tree_leaf _ ->
      (match live with
       | theorem :: remaining -> theorem,remaining
       | [] -> failwith "action296 adaptive forest: missing live leaf")
  | Candle_action296_forest_tree_split (axis,left,right) ->
      let left_theorem,after_left =
        candle_action296_forest_glue left live in
      let right_theorem,remaining =
        candle_action296_forest_glue right after_left in
      let glued =
        M_verifier.m_glue_cells_list candle_action296_plan_dimension axis
          left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass
        candle_action296_plan_dimension glued,remaining;;

let candle_action296_forest_result_shape theorem =
  M_verifier.dest_m_cell_list_pass (concl theorem);;

let candle_action296_forest_expected_domain domain =
  let actual,_,_ = M_taylor.dest_m_cell_domain (concl domain) in actual;;

let rec candle_action296_forest_validate_results roots results parents =
  match roots,results,parents with
  | [],[],[] -> true
  | (expected_index,_) :: remaining_roots,
    (actual_index,theorem) :: remaining_results,
    (parent_index,parent) :: remaining_parents ->
      let functions,proved_domain =
        candle_action296_forest_result_shape theorem in
      actual_index = expected_index &&
      parent_index = expected_index &&
      functions = [candle_action296_plan_prepared.function_term] &&
      aconv proved_domain
        (candle_action296_forest_expected_domain parent) &&
      hyp theorem = [] &&
      candle_action296_forest_validate_results
        remaining_roots remaining_results remaining_parents
  | _ -> false;;

let candle_action296_adaptive_forest_prove
    label roots expected_final_cells expected_digest =
  if roots = [] ||
     not (candle_action296_forest_strict_roots (-1) roots) then
    failwith "action296 adaptive forest: invalid root plan";
  let axioms_before = axioms () in
  let parents =
    map
      (fun (index,_) ->
        index,List.nth !candle_action296_leaf_grouping_leaves index)
      roots in
  let _ = candle_action296_forest_marker "source-preparation" "begin" in
  let prepared =
    candle_action296_forest_map2
      (fun (index,plan_data) (parent_index,parent) ->
        if index <> parent_index then
          failwith "action296 adaptive forest: parent index mismatch";
        let lower,upper =
          candle_action296_leaf_grouping_domain_bounds parent in
        {
          forest_prepared_index = index;
          forest_prepared_parent = parent;
          forest_prepared_plan_data = plan_data;
          forest_prepared_source =
            candle_q_dim_analytic_jet_prepare_box_six
              candle_action296_plan_prepared.function_term lower upper;
        })
      roots parents in
  let _ = candle_action296_forest_marker "source-preparation" "end" in
  let _ =
    candle_action296_forest_marker "point-plan-compilation" "begin" in
  let planned =
    map
      (fun source ->
        {
          forest_planned_index = source.forest_prepared_index;
          forest_planned_parent = source.forest_prepared_parent;
          forest_planned_plan_data = source.forest_prepared_plan_data;
          forest_planned_source = source.forest_prepared_source;
          forest_planned_point_plan =
            candle_q_dim_taylor_model_point_plan_six
              source.forest_prepared_source;
        })
      prepared in
  let _ = candle_action296_forest_marker "point-plan-compilation" "end" in
  let _ = candle_action296_forest_marker "final-cell-preparation" "begin" in
  let groups =
    map
      (fun source ->
        let tree =
          candle_action296_forest_build_tree
            source.forest_planned_parent source.forest_planned_plan_data in
        let domains = candle_action296_forest_tree_domains tree in
        {
          forest_group_index = source.forest_planned_index;
          forest_group_parent = source.forest_planned_parent;
          forest_group_prepared = source.forest_planned_source;
          forest_group_tree = tree;
          forest_group_domains = domains;
          forest_group_cells =
            map
              (fun domain ->
                candle_action296_forest_cell
                  (candle_action296_adaptive_grouping_case
                    source.forest_planned_source
                    source.forest_planned_point_plan domain))
              domains;
        })
      planned in
  let _ = candle_action296_forest_marker "final-cell-preparation" "end" in
  let final_cell_count =
    List.fold_left
      (fun count group -> count + length group.forest_group_cells)
      0 groups in
  if length groups <> length roots ||
     final_cell_count <> expected_final_cells then
    failwith "action296 adaptive forest: forest shape";
  let _ = candle_action296_forest_marker "aggregate-proofs" "begin" in
  let aggregate_results =
    map
      (fun group ->
        candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
          group.forest_group_prepared group.forest_group_cells)
      groups in
  let _ = candle_action296_forest_marker "aggregate-proofs" "end" in
  let _ = candle_action296_forest_marker "source-extraction" "begin" in
  let source_groups =
    candle_action296_forest_map2
      (fun result group ->
        map
          (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
            result)
          group.forest_group_cells)
      aggregate_results groups in
  let _ = candle_action296_forest_marker "source-extraction" "end" in
  let _ = candle_action296_forest_marker "live-handoff-and-glue" "begin" in
  let root_results =
    List.flatten
      (candle_action296_forest_map3
        (fun group sources domains ->
          let live =
            candle_action296_forest_map3
              candle_action296_forest_live
              group.forest_group_cells sources domains in
          let theorem,remaining =
            candle_action296_forest_glue group.forest_group_tree live in
          if remaining <> [] then
            failwith "action296 adaptive forest: trailing live leaves";
          [group.forest_group_index,theorem])
        groups source_groups
        (map (fun group -> group.forest_group_domains) groups)) in
  let _ = candle_action296_forest_marker "live-handoff-and-glue" "end" in
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
  if not
       (candle_action296_forest_validate_results roots root_results parents) ||
     not digest_matches ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith
      ("action296 adaptive forest: final validation failed for " ^ label);
  {
    forest_result_original_roots = length roots;
    forest_result_final_cells = final_cell_count;
    forest_result_theorems = root_results;
    forest_result_digest = digest;
  };;

let candle_action296_adaptive_forest_prove_one index plan_data =
  let phase = "leaf-" ^ string_of_int index in
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-source-preparation") "begin" in
  let prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term lower upper in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-source-preparation") "end" in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-point-plan-compilation") "begin" in
  let point_plan = candle_q_dim_taylor_model_point_plan_six prepared in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-point-plan-compilation") "end" in
  let tree = candle_action296_forest_build_tree parent plan_data in
  let domains = candle_action296_forest_tree_domains tree in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-final-cell-preparation") "begin" in
  let cells =
    map
      (fun domain ->
        candle_action296_forest_cell
          (candle_action296_adaptive_grouping_case
            prepared point_plan domain))
      domains in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-final-cell-preparation") "end" in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-aggregate-proof") "begin" in
  let aggregate =
    candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
      prepared cells in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-aggregate-proof") "end" in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-source-extraction") "begin" in
  let sources =
    map
      (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
        aggregate)
      cells in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-source-extraction") "end" in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-live-handoff-and-glue") "begin" in
  let live =
    candle_action296_forest_map3
      candle_action296_forest_live cells sources domains in
  let theorem,remaining = candle_action296_forest_glue tree live in
  let _ =
    candle_action296_forest_marker
      (phase ^ "-live-handoff-and-glue") "end" in
  if remaining <> [] ||
     not
       (candle_action296_forest_validate_results
         [index,plan_data] [index,theorem] [index,parent]) then
    failwith
      ("action296 adaptive forest: invalid sequential root " ^
       string_of_int index);
  index,theorem,length cells;;

let candle_action296_adaptive_forest_prove_sequential
    label roots expected_final_cells expected_digest =
  if roots = [] ||
     not (candle_action296_forest_strict_roots (-1) roots) then
    failwith "action296 adaptive forest: invalid sequential root plan";
  let axioms_before = axioms () in
  let _ = candle_action296_forest_marker "sequential-forest" "begin" in
  let completed =
    map
      (fun (index,plan_data) ->
        candle_action296_adaptive_forest_prove_one index plan_data)
      roots in
  let _ = candle_action296_forest_marker "sequential-forest" "end" in
  let root_results =
    map (fun (index,theorem,_) -> index,theorem) completed in
  let final_cell_count =
    List.fold_left
      (fun count (_,_,cells) -> count + cells) 0 completed in
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
  if final_cell_count <> expected_final_cells ||
     not digest_matches ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith
      ("action296 adaptive forest: sequential validation failed for " ^
       label);
  {
    forest_result_original_roots = length roots;
    forest_result_final_cells = final_cell_count;
    forest_result_theorems = root_results;
    forest_result_digest = digest;
  };;

end;;
