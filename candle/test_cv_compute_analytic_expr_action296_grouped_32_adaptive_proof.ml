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
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_tree_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree_six_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_tree;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_tree_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_prove;;
open Candle_cv_analytic_expr_taylor_model_tree_six_prove;;

let candle_action296_grouped_32_proof_axioms_before = axioms ();;

let candle_action296_grouped_32_proof_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-grouped-32-adaptive-proof" ^
     " scope=first-32 phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_grouped_32_proof_tree =
  | Candle_action296_grouped_32_proof_leaf of thm
  | Candle_action296_grouped_32_proof_split of
      thm * int * candle_action296_grouped_32_proof_tree *
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
    (domain,axis,
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
        (parent,first_axis,
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
  | Candle_action296_grouped_32_proof_split (_,_,left,right) ->
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

type candle_action296_grouped_32_proof_logical_tree_six = {
  grouped_32_proof_logical_term : term;
  grouped_32_proof_logical_well_formed : thm;
  grouped_32_proof_logical_domain : thm;
  grouped_32_proof_logical_lower : term list;
  grouped_32_proof_logical_upper : term list;
  grouped_32_proof_logical_boxes : term;
  grouped_32_proof_logical_cells :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list;
};;

let rec candle_action296_grouped_32_proof_logical_tree cells = function
  | Candle_action296_grouped_32_proof_leaf domain ->
      (match cells with
       | cell :: remaining ->
           let lower,upper =
             candle_action296_leaf_grouping_domain_bounds domain in
           if not
               (candle_action296_grouped_32_proof_aconv_lists
                  lower cell.fixed_algebraic_batch_lower &&
                candle_action296_grouped_32_proof_aconv_lists
                  upper cell.fixed_algebraic_batch_upper) then
             failwith
               "action296 grouped 32 proof: logical leaf/cell mismatch";
           let boxes = candle_poly_fixture_q_boxes lower upper in
           let tree =
             candle_q_dim_taylor_model_tree_leaf_term
               cell.fixed_algebraic_batch_center_variant.
                 variant_expression_term
               boxes in
           {
             grouped_32_proof_logical_term = tree;
             grouped_32_proof_logical_well_formed =
               candle_q_dim_taylor_model_tree_leaf_well_formed_six tree;
             grouped_32_proof_logical_domain = domain;
             grouped_32_proof_logical_lower = lower;
             grouped_32_proof_logical_upper = upper;
             grouped_32_proof_logical_boxes = boxes;
             grouped_32_proof_logical_cells = [cell];
           },remaining
       | [] ->
           failwith "action296 grouped 32 proof: missing logical leaf cell")
  | Candle_action296_grouped_32_proof_split
      (domain,axis,left,right) ->
      let left_logical,after_left =
        candle_action296_grouped_32_proof_logical_tree cells left in
      let right_logical,remaining =
        candle_action296_grouped_32_proof_logical_tree after_left right in
      let lower,upper =
        candle_action296_leaf_grouping_domain_bounds domain in
      let boxes = candle_poly_fixture_q_boxes lower upper in
      let tree,well_formed =
        candle_q_dim_taylor_model_tree_node_well_formed_six
          axis boxes lower upper
          left_logical.grouped_32_proof_logical_term
          left_logical.grouped_32_proof_logical_boxes
          left_logical.grouped_32_proof_logical_lower
          left_logical.grouped_32_proof_logical_upper
          left_logical.grouped_32_proof_logical_well_formed
          right_logical.grouped_32_proof_logical_term
          right_logical.grouped_32_proof_logical_boxes
          right_logical.grouped_32_proof_logical_lower
          right_logical.grouped_32_proof_logical_upper
          right_logical.grouped_32_proof_logical_well_formed in
      {
        grouped_32_proof_logical_term = tree;
        grouped_32_proof_logical_well_formed = well_formed;
        grouped_32_proof_logical_domain = domain;
        grouped_32_proof_logical_lower = lower;
        grouped_32_proof_logical_upper = upper;
        grouped_32_proof_logical_boxes = boxes;
        grouped_32_proof_logical_cells =
          left_logical.grouped_32_proof_logical_cells @
          right_logical.grouped_32_proof_logical_cells;
      },remaining;;

let rec candle_action296_grouped_32_proof_logical_trees cells = function
  | [] ->
      if cells = [] then []
      else failwith "action296 grouped 32 proof: trailing logical cells"
  | (index,tree) :: remaining_trees ->
      let phase = "tree-topology-" ^ string_of_int index in
      let _ = candle_action296_grouped_32_proof_marker phase "begin" in
      let logical,remaining_cells =
        candle_action296_grouped_32_proof_logical_tree cells tree in
      let _ = candle_action296_grouped_32_proof_marker phase "end" in
      (index,logical) ::
      candle_action296_grouped_32_proof_logical_trees
        remaining_cells remaining_trees;;

let _ = candle_action296_grouped_32_proof_marker "tree-topologies" "begin";;
let candle_action296_grouped_32_proof_logical_groups_ref :
    (int * candle_action296_grouped_32_proof_logical_tree_six) list list
      option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_logical_groups_ref :=
    Some
      (map
        (fun group ->
          candle_action296_grouped_32_proof_logical_trees
            group.grouped_32_proof_cells group.grouped_32_proof_trees)
        (candle_action296_grouped_32_proof_groups ()));;
let _ = candle_action296_grouped_32_proof_marker "tree-topologies" "end";;

let candle_action296_grouped_32_proof_logical_groups () =
  match !candle_action296_grouped_32_proof_logical_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 grouped 32 proof: missing logical trees";;

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

let candle_action296_grouped_32_proof_append_function =
  `APPEND:
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list->
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list->
     (candle_analytic_expr#
       (((num#num)#num)#((num#num)#num))list)list`;;

let candle_action296_grouped_32_proof_narrow_result result tree_accept
    tree_jobs =
  {
    fixed_algebraic_batch_box_prepared =
      result.fixed_algebraic_batch_box_prepared;
    fixed_algebraic_batch_jobs_term = tree_jobs;
    fixed_algebraic_batch_encoded_jobs_term =
      result.fixed_algebraic_batch_encoded_jobs_term;
    fixed_algebraic_batch_accept_theorem = tree_accept;
    fixed_algebraic_batch_cells = [];
  };;

let candle_action296_grouped_32_proof_root_live source logical =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_grouped_32_proof_aconv_lists
             lower logical.grouped_32_proof_logical_lower &&
           candle_action296_grouped_32_proof_aconv_lists
             upper logical.grouped_32_proof_logical_upper) then
        failwith "action296 grouped 32 proof: unexpected root handoff box";
      source)
    logical.grouped_32_proof_logical_domain;;

let rec candle_action296_grouped_32_proof_project_trees
    result remaining_jobs remaining_accept = function
  | [] ->
      [],remaining_jobs,remaining_accept
  | (index,logical) :: remaining_trees ->
      let jobs_call =
        mk_comb
          (`candle_q_dim_taylor_model_tree_jobs`,
           logical.grouped_32_proof_logical_term) in
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
           (candle_action296_grouped_32_proof_aconv_lists
             tree_items (fst (chop_list tree_count remaining_items))) then
        failwith "action296 grouped 32 proof: non-prefix tree jobs";
      let _,suffix_items = chop_list tree_count remaining_items in
      let job_type = type_of (hd remaining_items) in
      let suffix_jobs = mk_list (suffix_items,job_type) in
      let append_call =
        list_mk_comb
          (candle_action296_grouped_32_proof_append_function,
           [tree_jobs;suffix_jobs]) in
      let append_expansion = REWRITE_CONV [APPEND] append_call in
      if hyp append_expansion <> [] ||
         not (aconv (rand (concl append_expansion)) remaining_jobs) then
        failwith "action296 grouped 32 proof: append expansion mismatch";
      let split_accept =
        REWRITE_RULE
          [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_append]
          (REWRITE_RULE [SYM append_expansion] remaining_accept) in
      let tree_accept,suffix_accept =
        if suffix_items = [] then begin
          if remaining_trees <> [] || not (aconv tree_jobs remaining_jobs) then
            failwith
              "action296 grouped 32 proof: malformed terminal tree projection";
          remaining_accept,remaining_accept
        end else
          CONJ_PAIR split_accept in
      let narrowed =
        candle_action296_grouped_32_proof_narrow_result
          result tree_accept tree_jobs in
      let source =
        candle_q_dim_taylor_model_fixed_algebraic_tree_source_six
          narrowed logical.grouped_32_proof_logical_term
          logical.grouped_32_proof_logical_well_formed in
      let live =
        candle_action296_grouped_32_proof_root_live source logical in
      let projected,final_jobs,final_accept =
        candle_action296_grouped_32_proof_project_trees
          result suffix_jobs suffix_accept remaining_trees in
      (index,live) :: projected,final_jobs,final_accept;;

let candle_action296_grouped_32_proof_project_group result logical_trees =
  let projected,remaining_jobs,_ =
    candle_action296_grouped_32_proof_project_trees
      result result.fixed_algebraic_batch_jobs_term
      result.fixed_algebraic_batch_accept_theorem logical_trees in
  if dest_list remaining_jobs <> [] then
    failwith "action296 grouped 32 proof: unconsumed aggregate jobs";
  projected;;

let _ =
  candle_action296_grouped_32_proof_marker "tree-root-handoffs" "begin";;
let candle_action296_grouped_32_proof_leaf_results_ref :
    (int * thm) list option ref = ref None;;
let _ =
  candle_action296_grouped_32_proof_leaf_results_ref :=
    Some
      (List.flatten
        (candle_action296_grouped_32_split_scan_map2
          candle_action296_grouped_32_proof_project_group
          (candle_action296_grouped_32_proof_results ())
          (candle_action296_grouped_32_proof_logical_groups ())));;
let _ =
  candle_action296_grouped_32_proof_marker "tree-root-handoffs" "end";;

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
