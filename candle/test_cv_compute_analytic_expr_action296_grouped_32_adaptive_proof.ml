(* ========================================================================== *)
(* Proof-producing adaptive forest over 32 genuine action-296 NL leaves.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The pinned whole-leaf and split scans are     *)
(* untrusted plan preparation.  This file rechecks only the selected final   *)
(* cells through the aggregate proof adapter and glues them to the original  *)
(* 32 live Flyspeck domains.                                                  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_depth2_scan_algebraic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

let candle_action296_grouped_32_proof_axioms_before = axioms ();;

let candle_action296_grouped_32_proof_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-grouped-32-adaptive-proof" ^
     " scope=first-32 phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_grouped_32_proof_tree =
  | Candle_action296_grouped_32_proof_leaf of thm
  | Candle_action296_grouped_32_proof_split of
      int * candle_action296_grouped_32_proof_tree *
      candle_action296_grouped_32_proof_tree;;

type candle_action296_grouped_32_proof_group_six = {
  grouped_32_proof_prepared : candle_q_dim_analytic_jet_prepared_six;
  grouped_32_proof_trees :
    (int * candle_action296_grouped_32_proof_tree) list;
  grouped_32_proof_domains : thm list;
  grouped_32_proof_cells :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list;
};;

let rec candle_action296_grouped_32_proof_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_grouped_32_proof_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_action296_grouped_32_proof_preferred_axis axes =
  if List.mem 4 axes then 4 else
  match axes with
  | axis :: _ -> axis
  | [] -> failwith "action296 grouped 32 proof: no viable axis";;

let candle_action296_grouped_32_proof_split axis domain =
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 axis domain in
  Candle_action296_grouped_32_proof_split
    (axis,
     Candle_action296_grouped_32_proof_leaf left,
     Candle_action296_grouped_32_proof_leaf right);;

let rec candle_action296_grouped_32_proof_find_depth2 index branch = function
  | [] -> failwith "action296 grouped 32 proof: depth2 result not found"
  | (intermediate,flags) :: remaining ->
      if intermediate.grouped_32_depth2_parent_index = index &&
         intermediate.grouped_32_depth2_branch = branch then
        intermediate,flags
      else
        candle_action296_grouped_32_proof_find_depth2
          index branch remaining;;

let candle_action296_grouped_32_proof_hard_child
    index branch domain accepted =
  if accepted then Candle_action296_grouped_32_proof_leaf domain else
  let _,raw_flags =
    candle_action296_grouped_32_proof_find_depth2 index branch
      (candle_action296_grouped_32_depth2_results ()) in
  let viable_axes =
    candle_action296_grouped_32_split_scan_viable_axes
      (candle_action296_grouped_32_split_scan_bools raw_flags) in
  candle_action296_grouped_32_proof_split
    (candle_action296_grouped_32_proof_preferred_axis viable_axes) domain;;

let candle_action296_grouped_32_proof_hard_tree index parent first_axis flags =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 first_axis parent in
  let first_flags =
    candle_action296_grouped_32_depth2_drop (2 * (first_axis - 1)) flags in
  match first_flags with
  | left_flag :: right_flag :: _ ->
      Candle_action296_grouped_32_proof_split
        (first_axis,
         candle_action296_grouped_32_proof_hard_child
           index 0 left left_flag,
         candle_action296_grouped_32_proof_hard_child
           index 1 right right_flag)
  | _ -> failwith "action296 grouped 32 proof: hard first-child shape";;

let candle_action296_grouped_32_proof_tree index parent =
  let whole_flag =
    List.nth (candle_action296_grouped_32_flags ()) index in
  if candle_action296_adaptive_grouping_flag_string whole_flag = "1" then
    Candle_action296_grouped_32_proof_leaf parent
  else
    let _,raw_flags =
      candle_action296_grouped_32_depth2_find_result index
        (candle_action296_grouped_32_split_scan_results ()) in
    let flags =
      candle_action296_grouped_32_split_scan_bools raw_flags in
    let viable_axes =
      candle_action296_grouped_32_split_scan_viable_axes flags in
    if viable_axes <> [] then
      candle_action296_grouped_32_proof_split
        (candle_action296_grouped_32_proof_preferred_axis viable_axes) parent
    else
      let first_axis =
        try assoc index candle_action296_grouped_32_depth2_policies
        with Failure _ ->
          failwith "action296 grouped 32 proof: missing hard policy" in
      candle_action296_grouped_32_proof_hard_tree
        index parent first_axis flags;;

let rec candle_action296_grouped_32_proof_tree_domains = function
  | Candle_action296_grouped_32_proof_leaf domain -> [domain]
  | Candle_action296_grouped_32_proof_split (_,left,right) ->
      candle_action296_grouped_32_proof_tree_domains left @
      candle_action296_grouped_32_proof_tree_domains right;;

let candle_action296_grouped_32_proof_cell case =
  {
    fixed_algebraic_batch_center_variant =
      case.adaptive_grouping_center_variant;
    fixed_algebraic_batch_lower = case.adaptive_grouping_lower;
    fixed_algebraic_batch_upper = case.adaptive_grouping_upper;
  };;

let candle_action296_grouped_32_proof_case_for_domain candidates domain =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain in
  try
    find
      (fun case ->
        candle_action296_grouped_32_proof_aconv_lists
          lower case.adaptive_grouping_lower &&
        candle_action296_grouped_32_proof_aconv_lists
          upper case.adaptive_grouping_upper)
      candidates
  with Not_found ->
    failwith "action296 grouped 32 proof: prepared final cell not found";;

let candle_action296_grouped_32_proof_depth2_cases prepared =
  List.flatten
    (map
      (fun job ->
        if aconv
             job.grouped_32_depth2_job_prepared.expression_term
             prepared.expression_term then
          job.grouped_32_depth2_job_cases
        else [])
      (candle_action296_grouped_32_depth2_jobs ()));;

let rec candle_action296_grouped_32_proof_map3 action left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head :: left_tail,middle_head :: middle_tail,
    right_head :: right_tail ->
      action left_head middle_head right_head ::
      candle_action296_grouped_32_proof_map3
        action left_tail middle_tail right_tail
  | _ -> failwith "action296 grouped 32 proof: group shape";;

let rec candle_action296_grouped_32_proof_index_domains index = function
  | [] -> []
  | domain :: remaining ->
      (index,domain) ::
      candle_action296_grouped_32_proof_index_domains
        (index + 1) remaining;;

let rec candle_action296_grouped_32_proof_index_plans offset = function
  | [] -> []
  | (domains,prepared,_) :: remaining ->
      (candle_action296_grouped_32_proof_index_domains offset domains,
       prepared) ::
      candle_action296_grouped_32_proof_index_plans
        (offset + length domains) remaining;;

let _ = candle_action296_grouped_32_proof_marker "cell-reuse" "begin";;
let candle_action296_grouped_32_proof_groups_ref :
    candle_action296_grouped_32_proof_group_six list option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_groups_ref :=
    Some
      (candle_action296_grouped_32_proof_map3
        (fun (indexed_parents,prepared) (_,whole_cases) split_job ->
          let indexed_trees =
            map
              (fun (index,parent) ->
                index,candle_action296_grouped_32_proof_tree index parent)
              indexed_parents in
          let domains =
            List.flatten
              (map
                (fun (_,tree) ->
                  candle_action296_grouped_32_proof_tree_domains tree)
                indexed_trees) in
          let candidates =
            whole_cases @ split_job.grouped_32_split_scan_job_cases @
            candle_action296_grouped_32_proof_depth2_cases
              prepared in
          {
            grouped_32_proof_prepared = prepared;
            grouped_32_proof_trees = indexed_trees;
            grouped_32_proof_domains = domains;
            grouped_32_proof_cells =
              map
                (fun domain ->
                  candle_action296_grouped_32_proof_cell
                    (candle_action296_grouped_32_proof_case_for_domain
                      candidates domain))
                domains;
          })
        (candle_action296_grouped_32_proof_index_plans 0
          (candle_action296_grouped_32_plans ()))
        (candle_action296_grouped_32_jobs ())
        (candle_action296_grouped_32_split_scan_jobs ()));;
let _ = candle_action296_grouped_32_proof_marker "cell-reuse" "end";;

let candle_action296_grouped_32_proof_groups () =
  match !candle_action296_grouped_32_proof_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 grouped 32 proof: missing groups";;

let candle_action296_grouped_32_proof_final_cell_count =
  List.fold_left
    (fun count group -> count + length group.grouped_32_proof_domains)
    0 (candle_action296_grouped_32_proof_groups ());;

if length (candle_action296_grouped_32_proof_groups ()) <> 12 ||
   candle_action296_grouped_32_proof_final_cell_count <> 60 then
  failwith "action296 grouped 32 proof: adaptive forest shape";;

let _ = candle_action296_grouped_32_proof_marker "aggregate-proofs" "begin";;
let candle_action296_grouped_32_proof_results_ref :
    candle_q_dim_taylor_model_fixed_algebraic_batch_result_six list
      option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_results_ref :=
    Some
      (map
        (fun group ->
          candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
            group.grouped_32_proof_prepared
            group.grouped_32_proof_cells)
        (candle_action296_grouped_32_proof_groups ()));;
let _ = candle_action296_grouped_32_proof_marker "aggregate-proofs" "end";;

let candle_action296_grouped_32_proof_results () =
  match !candle_action296_grouped_32_proof_results_ref with
  | Some results -> results
  | None -> failwith "action296 grouped 32 proof: missing aggregate results";;

let _ = candle_action296_grouped_32_proof_marker "source-extraction" "begin";;
let candle_action296_grouped_32_proof_source_groups_ref :
    thm list list option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_source_groups_ref :=
    Some
      (map2
        (fun result group ->
          map
            (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
              result)
            group.grouped_32_proof_cells)
        (candle_action296_grouped_32_proof_results ())
        (candle_action296_grouped_32_proof_groups ()));;
let _ = candle_action296_grouped_32_proof_marker "source-extraction" "end";;

let candle_action296_grouped_32_proof_source_groups () =
  match !candle_action296_grouped_32_proof_source_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 grouped 32 proof: missing sources";;

let candle_action296_grouped_32_proof_live cell source domain =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_grouped_32_proof_aconv_lists
             lower cell.fixed_algebraic_batch_lower &&
           candle_action296_grouped_32_proof_aconv_lists
             upper cell.fixed_algebraic_batch_upper) then
        failwith "action296 grouped 32 proof: unexpected handoff box";
      source)
    domain;;

let _ =
  candle_action296_grouped_32_proof_marker "live-handoff-and-glue" "begin";;
let candle_action296_grouped_32_proof_live_groups_ref :
    thm list list option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_live_groups_ref :=
    Some
      (candle_action296_grouped_32_proof_map3
        (fun group sources domains ->
          candle_action296_grouped_32_proof_map3
            candle_action296_grouped_32_proof_live
            group.grouped_32_proof_cells sources domains)
        (candle_action296_grouped_32_proof_groups ())
        (candle_action296_grouped_32_proof_source_groups ())
        (map
          (fun group -> group.grouped_32_proof_domains)
          (candle_action296_grouped_32_proof_groups ())));;

let candle_action296_grouped_32_proof_live_groups () =
  match !candle_action296_grouped_32_proof_live_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 grouped 32 proof: missing live cells";;

let rec candle_action296_grouped_32_proof_glue tree live =
  match tree with
  | Candle_action296_grouped_32_proof_leaf _ ->
      (match live with
       | theorem :: remaining -> theorem,remaining
       | [] -> failwith "action296 grouped 32 proof: missing live leaf")
  | Candle_action296_grouped_32_proof_split (axis,left,right) ->
      let left_theorem,after_left =
        candle_action296_grouped_32_proof_glue left live in
      let right_theorem,remaining =
        candle_action296_grouped_32_proof_glue right after_left in
      let glued =
        M_verifier.m_glue_cells_list candle_action296_plan_dimension axis
          left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass
        candle_action296_plan_dimension glued,remaining;;

let rec candle_action296_grouped_32_proof_glue_trees trees live =
  match trees with
  | [] ->
      if live = [] then []
      else failwith "action296 grouped 32 proof: trailing live leaves"
  | (index,tree) :: remaining_trees ->
      let theorem,remaining_live =
        candle_action296_grouped_32_proof_glue tree live in
      (index,theorem) ::
      candle_action296_grouped_32_proof_glue_trees
        remaining_trees remaining_live;;

let candle_action296_grouped_32_proof_leaf_results_ref :
    (int * thm) list option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_leaf_results_ref :=
    Some
      (List.flatten
        (candle_action296_grouped_32_split_scan_map2
          (fun group live ->
            candle_action296_grouped_32_proof_glue_trees
              group.grouped_32_proof_trees live)
          (candle_action296_grouped_32_proof_groups ())
          (candle_action296_grouped_32_proof_live_groups ())));;
let _ =
  candle_action296_grouped_32_proof_marker "live-handoff-and-glue" "end";;

let candle_action296_grouped_32_proof_leaf_results () =
  match !candle_action296_grouped_32_proof_leaf_results_ref with
  | Some results -> results
  | None -> failwith "action296 grouped 32 proof: missing leaf results";;

let candle_action296_grouped_32_proof_result_shape theorem =
  M_verifier.dest_m_cell_list_pass (concl theorem);;

let candle_action296_grouped_32_proof_expected_domain domain =
  let actual,_,_ = M_taylor.dest_m_cell_domain (concl domain) in actual;;

let rec candle_action296_grouped_32_proof_validate index results domains =
  match results,domains with
  | [],[] -> true
  | (actual_index,theorem) :: remaining_results,
    domain :: remaining_domains ->
      let functions,proved_domain =
        candle_action296_grouped_32_proof_result_shape theorem in
      actual_index = index &&
      functions = [candle_action296_plan_prepared.function_term] &&
      aconv proved_domain
        (candle_action296_grouped_32_proof_expected_domain domain) &&
      hyp theorem = [] &&
      candle_action296_grouped_32_proof_validate
        (index + 1) remaining_results remaining_domains
  | _ -> false;;

let candle_action296_grouped_32_proof_digest =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map
          (fun (_,theorem) -> string_of_thm theorem)
          (candle_action296_grouped_32_proof_leaf_results ()))));;

let candle_action296_grouped_32_proof_axioms_after = axioms ();;

if not
     (candle_action296_grouped_32_proof_validate 0
       (candle_action296_grouped_32_proof_leaf_results ())
       candle_action296_grouped_32_domains) ||
   candle_action296_grouped_32_proof_digest <>
     "7f5df8d12a23b58b73fee9e254b83753" ||
   length candle_action296_grouped_32_proof_axioms_after <>
     length candle_action296_grouped_32_proof_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_grouped_32_proof_axioms_before)
       candle_action296_grouped_32_proof_axioms_after) then
  failwith "action296 grouped 32 proof: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_ADAPTIVE_PROOF_RESULT" ^
   " original_leaves=32 final_cells=" ^
   string_of_int candle_action296_grouped_32_proof_final_cell_count ^
   " shared_preparations=12 computes=12 theorem_digest=" ^
   candle_action296_grouped_32_proof_digest);;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_ADAPTIVE_PROOF_OK DEVELOPMENT_NON_RELEASE";;
