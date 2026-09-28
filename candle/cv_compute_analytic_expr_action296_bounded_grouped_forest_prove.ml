(* ========================================================================== *)
(* Bounded preparation-sharing proof adapter for action-296 leaf forests.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Consecutive roots first attempt to share one  *)
(* authenticated source envelope and point plan.  A failed untrusted grouping *)
(* attempt is split recursively; singleton roots still fail closed.  Every    *)
(* successful final cell is recomputed by the existing reflected proof        *)
(* adapter, transported to its exact Flyspeck box, and glued to its original  *)
(* root.                                                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_adaptive_forest_prove.ml";;

module Candle_cv_action296_bounded_grouped_forest_prove = struct

open Candle_cv_action296_adaptive_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

type candle_action296_bounded_group_root_six = {
  bounded_group_root_index : int;
  bounded_group_root_parent : thm;
  bounded_group_root_tree : candle_action296_forest_tree;
  bounded_group_root_domains : thm list;
  bounded_group_root_cells :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list;
};;

type candle_action296_bounded_group_outcome = {
  bounded_group_results : (int * thm) list;
  bounded_group_final_cells : int;
  bounded_group_attempts : int;
  bounded_group_successes : int;
  bounded_group_sizes : int list;
};;

type candle_action296_bounded_group_result = {
  bounded_group_forest_result : candle_action296_forest_result;
  bounded_group_attempts_total : int;
  bounded_group_successes_total : int;
  bounded_group_successful_sizes : int list;
};;

let candle_action296_bounded_group_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-bounded-grouped-forest-proof" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_bounded_group_profile phase operation =
  let _ = candle_action296_bounded_group_marker phase "begin" in
  try
    let result = operation () in
    let _ = candle_action296_bounded_group_marker phase "end" in
    result
  with Failure message ->
    let _ = candle_action296_bounded_group_marker phase "end" in
    failwith message;;

let rec candle_action296_bounded_group_take count items =
  if count <= 0 then [],items else
  match items with
  | [] -> [],[]
  | head :: tail ->
      let selected,remaining =
        candle_action296_bounded_group_take (count - 1) tail in
      head :: selected,remaining;;

let rec candle_action296_bounded_group_partition size items =
  if size <= 0 then
    failwith "action296 bounded grouping: nonpositive group size"
  else
    match items with
    | [] -> []
    | _ ->
        let selected,remaining =
          candle_action296_bounded_group_take size items in
        selected ::
          candle_action296_bounded_group_partition size remaining;;

let candle_action296_bounded_group_split items =
  let size = length items in
  if size <= 1 then
    failwith "action296 bounded grouping: cannot split singleton";
  let left_size = size / 2 in
  candle_action296_bounded_group_take left_size items;;

let candle_action296_bounded_group_phase attempt roots suffix =
  let first = fst (hd roots) and last = fst (hd (rev roots)) in
  "attempt-" ^ string_of_int attempt ^ "-roots-" ^
  string_of_int first ^ "-" ^ string_of_int last ^ "-" ^ suffix;;

let candle_action296_bounded_group_root prepared point_plan
    (index,plan_data) =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let tree = candle_action296_forest_build_tree parent plan_data in
  let domains = candle_action296_forest_tree_domains tree in
  {
    bounded_group_root_index = index;
    bounded_group_root_parent = parent;
    bounded_group_root_tree = tree;
    bounded_group_root_domains = domains;
    bounded_group_root_cells =
      map
        (fun domain ->
          candle_action296_forest_cell
            (candle_action296_adaptive_grouping_case
              prepared point_plan domain))
        domains;
  };;

let rec candle_action296_bounded_group_consume_sources sources roots =
  match roots with
  | [] ->
      if sources = [] then []
      else failwith "action296 bounded grouping: trailing source theorems"
  | root :: remaining_roots ->
      let count = length root.bounded_group_root_domains in
      let selected,remaining_sources =
        candle_action296_bounded_group_take count sources in
      if length selected <> count then
        failwith "action296 bounded grouping: missing source theorems";
      let live =
        candle_action296_forest_map3
          candle_action296_forest_live
          root.bounded_group_root_cells selected
          root.bounded_group_root_domains in
      let theorem,trailing =
        candle_action296_forest_glue root.bounded_group_root_tree live in
      if trailing <> [] then
        failwith "action296 bounded grouping: trailing live leaves";
      (root.bounded_group_root_index,theorem) ::
        candle_action296_bounded_group_consume_sources
          remaining_sources remaining_roots;;

let candle_action296_bounded_group_prove_attempt attempt roots =
  if roots = [] then failwith "action296 bounded grouping: empty attempt";
  let parents =
    map
      (fun (index,_) ->
        index,List.nth !candle_action296_leaf_grouping_leaves index)
      roots in
  let phase suffix =
    candle_action296_bounded_group_phase attempt roots suffix in
  let prepared =
    candle_action296_bounded_group_profile (phase "source-preparation")
      (fun () ->
        let lower,upper =
          candle_action296_leaf_grouping_envelope (map snd parents) in
        candle_q_dim_analytic_jet_prepare_box_six
          candle_action296_plan_prepared.function_term lower upper) in
  let point_plan =
    candle_action296_bounded_group_profile (phase "point-plan-reuse")
      (fun () -> candle_action296_forest_point_plan) in
  let grouped_roots,cells =
    candle_action296_bounded_group_profile (phase "final-cell-preparation")
      (fun () ->
        let grouped_roots =
          map (candle_action296_bounded_group_root prepared point_plan)
            roots in
        let cells =
          List.flatten
            (map
              (fun root -> root.bounded_group_root_cells)
              grouped_roots) in
        grouped_roots,cells) in
  let aggregate =
    candle_action296_bounded_group_profile (phase "aggregate-proof")
      (fun () ->
        candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
          prepared cells) in
  let sources =
    candle_action296_bounded_group_profile (phase "source-extraction")
      (fun () ->
        map
          (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
            aggregate)
          cells) in
  let results =
    candle_action296_bounded_group_profile (phase "live-handoff-and-glue")
      (fun () ->
        candle_action296_bounded_group_consume_sources
          sources grouped_roots) in
  if not (candle_action296_forest_validate_results roots results parents) then
    failwith "action296 bounded grouping: group result validation";
  results,length cells;;

let candle_action296_bounded_group_append left right =
  {
    bounded_group_results =
      left.bounded_group_results @ right.bounded_group_results;
    bounded_group_final_cells =
      left.bounded_group_final_cells + right.bounded_group_final_cells;
    bounded_group_attempts =
      left.bounded_group_attempts + right.bounded_group_attempts;
    bounded_group_successes =
      left.bounded_group_successes + right.bounded_group_successes;
    bounded_group_sizes =
      left.bounded_group_sizes @ right.bounded_group_sizes;
  };;

let candle_action296_bounded_group_attempt_counter = ref 0;;

let rec candle_action296_bounded_group_prove roots =
  candle_action296_bounded_group_attempt_counter :=
    !candle_action296_bounded_group_attempt_counter + 1;
  let attempt = !candle_action296_bounded_group_attempt_counter in
  try
    let results,cells =
      candle_action296_bounded_group_prove_attempt attempt roots in
    {
      bounded_group_results = results;
      bounded_group_final_cells = cells;
      bounded_group_attempts = 1;
      bounded_group_successes = 1;
      bounded_group_sizes = [length roots];
    }
  with Failure message ->
    if length roots = 1 then
      failwith
        ("action296 bounded grouping: singleton failed: " ^ message)
    else
      let first = fst (hd roots) and last = fst (hd (rev roots)) in
      let _ =
        print_endline
          ("CANDLE_CV_ACTION296_BOUNDED_GROUP_FALLBACK" ^
           " roots=" ^ string_of_int first ^ "-" ^ string_of_int last ^
           " reason=" ^ message) in
      let left,right = candle_action296_bounded_group_split roots in
      let combined =
        candle_action296_bounded_group_append
          (candle_action296_bounded_group_prove left)
          (candle_action296_bounded_group_prove right) in
      {combined with
       bounded_group_attempts = combined.bounded_group_attempts + 1};;

let candle_action296_bounded_group_prove_chunks group_size roots =
  List.fold_left
    (fun accumulated group ->
      candle_action296_bounded_group_append accumulated
        (candle_action296_bounded_group_prove group))
    {
      bounded_group_results = [];
      bounded_group_final_cells = 0;
      bounded_group_attempts = 0;
      bounded_group_successes = 0;
      bounded_group_sizes = [];
    }
    (candle_action296_bounded_group_partition group_size roots);;

let candle_action296_bounded_group_prove_exact roots =
  candle_action296_bounded_group_attempt_counter :=
    !candle_action296_bounded_group_attempt_counter + 1;
  let attempt = !candle_action296_bounded_group_attempt_counter in
  let results,cells =
    candle_action296_bounded_group_prove_attempt attempt roots in
  {
    bounded_group_results = results;
    bounded_group_final_cells = cells;
    bounded_group_attempts = 1;
    bounded_group_successes = 1;
    bounded_group_sizes = [length roots];
  };;

let rec candle_action296_bounded_group_partition_sizes sizes roots =
  match sizes with
  | [] ->
      if roots = [] then []
      else failwith "action296 bounded grouping: trailing roots"
  | size :: remaining_sizes ->
      if size <= 0 then
        failwith "action296 bounded grouping: nonpositive pinned group size";
      let selected,remaining_roots =
        candle_action296_bounded_group_take size roots in
      if length selected <> size then
        failwith "action296 bounded grouping: pinned group exceeds roots";
      selected ::
        candle_action296_bounded_group_partition_sizes
          remaining_sizes remaining_roots;;

let candle_action296_bounded_group_prove_sizes sizes roots =
  List.fold_left
    (fun accumulated group ->
      candle_action296_bounded_group_append accumulated
        (candle_action296_bounded_group_prove_exact group))
    {
      bounded_group_results = [];
      bounded_group_final_cells = 0;
      bounded_group_attempts = 0;
      bounded_group_successes = 0;
      bounded_group_sizes = [];
    }
    (candle_action296_bounded_group_partition_sizes sizes roots);;

let candle_action296_bounded_grouped_forest_run
    label roots expected_final_cells expected_digest operation =
  if roots = [] ||
     not (candle_action296_forest_strict_roots (-1) roots) then
    failwith "action296 bounded grouping: invalid root plan";
  let axioms_before = axioms () in
  candle_action296_bounded_group_attempt_counter := 0;
  let _ = candle_action296_bounded_group_marker "bounded-forest" "begin" in
  let outcome = operation () in
  let _ = candle_action296_bounded_group_marker "bounded-forest" "end" in
  let digest =
    Digest.to_hex
      (Digest.string
        (String.concat "\n"
          (map
            (fun (_,theorem) -> string_of_thm theorem)
            outcome.bounded_group_results))) in
  let digest_matches =
    match expected_digest with
    | None -> true
    | Some expected -> digest = expected in
  let axioms_after = axioms () in
  if length outcome.bounded_group_results <> length roots ||
     outcome.bounded_group_final_cells <> expected_final_cells ||
     not digest_matches ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith
      ("action296 bounded grouping: final validation failed for " ^ label);
  {
    bounded_group_forest_result = {
      forest_result_original_roots = length roots;
      forest_result_final_cells = outcome.bounded_group_final_cells;
      forest_result_theorems = outcome.bounded_group_results;
      forest_result_digest = digest;
    };
    bounded_group_attempts_total = outcome.bounded_group_attempts;
    bounded_group_successes_total = outcome.bounded_group_successes;
    bounded_group_successful_sizes = outcome.bounded_group_sizes;
  };;

let candle_action296_bounded_grouped_forest_prove
    label group_size roots expected_final_cells expected_digest =
  candle_action296_bounded_grouped_forest_run
    label roots expected_final_cells expected_digest
    (fun () ->
      candle_action296_bounded_group_prove_chunks group_size roots);;

let candle_action296_bounded_grouped_forest_prove_sizes
    label sizes roots expected_final_cells expected_digest =
  candle_action296_bounded_grouped_forest_run
    label roots expected_final_cells expected_digest
    (fun () -> candle_action296_bounded_group_prove_sizes sizes roots);;

end;;
