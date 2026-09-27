(* ========================================================================== *)
(* Proof-producing adaptive forest over 16 stratified action-296 NL leaves. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The split policy is untrusted plan data.      *)
(* Every selected final cell is rechecked by the reflected aggregate proof   *)
(* adapter before exact Flyspeck split/glue reconstructs the 16 source roots. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_grouped_32_depth2_scan_algebraic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

let candle_action296_stratified_16_proof_axioms_before = axioms ();;

let candle_action296_stratified_16_proof_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stratified-16-adaptive-proof" ^
     " scope=midpoint-leaves phase=" ^ phase ^ " event=" ^ event);;

type candle_action296_stratified_16_proof_tree =
  | Candle_action296_stratified_16_proof_leaf of thm
  | Candle_action296_stratified_16_proof_split of
      int * candle_action296_stratified_16_proof_tree *
      candle_action296_stratified_16_proof_tree;;

type candle_action296_stratified_16_proof_policy =
  | Candle_action296_stratified_16_proof_direct
  | Candle_action296_stratified_16_proof_one_split of int
  | Candle_action296_stratified_16_proof_left_depth_two of int * int;;

type candle_action296_stratified_16_proof_prepared_six = {
  stratified_16_proof_index : int;
  stratified_16_proof_parent : thm;
  stratified_16_proof_prepared : candle_q_dim_analytic_jet_prepared_six;
};;

type candle_action296_stratified_16_proof_planned_six = {
  stratified_16_proof_planned_index : int;
  stratified_16_proof_planned_parent : thm;
  stratified_16_proof_planned_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  stratified_16_proof_plan : candle_q_dim_taylor_model_point_plan_six;
};;

type candle_action296_stratified_16_proof_group_six = {
  stratified_16_proof_group_index : int;
  stratified_16_proof_group_parent : thm;
  stratified_16_proof_group_prepared :
    candle_q_dim_analytic_jet_prepared_six;
  stratified_16_proof_group_tree :
    candle_action296_stratified_16_proof_tree;
  stratified_16_proof_group_domains : thm list;
  stratified_16_proof_group_cells :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list;
};;

let candle_action296_stratified_16_proof_indices =
  [33;99;165;232;298;364;431;497;
   563;629;696;762;828;895;961;1027];;

let candle_action296_stratified_16_proof_policies =
  [(33,Candle_action296_stratified_16_proof_one_split 4);
   (99,Candle_action296_stratified_16_proof_direct);
   (165,Candle_action296_stratified_16_proof_direct);
   (232,Candle_action296_stratified_16_proof_direct);
   (298,Candle_action296_stratified_16_proof_direct);
   (364,Candle_action296_stratified_16_proof_one_split 4);
   (431,Candle_action296_stratified_16_proof_one_split 4);
   (497,Candle_action296_stratified_16_proof_one_split 4);
   (563,Candle_action296_stratified_16_proof_direct);
   (629,Candle_action296_stratified_16_proof_one_split 4);
   (696,Candle_action296_stratified_16_proof_left_depth_two (6,4));
   (762,Candle_action296_stratified_16_proof_one_split 4);
   (828,Candle_action296_stratified_16_proof_direct);
   (895,Candle_action296_stratified_16_proof_direct);
   (961,Candle_action296_stratified_16_proof_one_split 1);
   (1027,Candle_action296_stratified_16_proof_one_split 1)];;

let rec candle_action296_stratified_16_proof_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_stratified_16_proof_aconv_lists left_tail right_tail
  | _ -> false;;

let rec candle_action296_stratified_16_proof_map2 action left right =
  match left,right with
  | [],[] -> []
  | left_head :: left_tail,right_head :: right_tail ->
      action left_head right_head ::
      candle_action296_stratified_16_proof_map2 action left_tail right_tail
  | _ -> failwith "action296 stratified 16 proof: map2 shape";;

let rec candle_action296_stratified_16_proof_map3 action left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head :: left_tail,middle_head :: middle_tail,
    right_head :: right_tail ->
      action left_head middle_head right_head ::
      candle_action296_stratified_16_proof_map3
        action left_tail middle_tail right_tail
  | _ -> failwith "action296 stratified 16 proof: map3 shape";;

let candle_action296_stratified_16_proof_split axis domain =
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 axis domain in
  Candle_action296_stratified_16_proof_split
    (axis,
     Candle_action296_stratified_16_proof_leaf left,
     Candle_action296_stratified_16_proof_leaf right);;

let candle_action296_stratified_16_proof_tree index parent =
  let policy =
    try assoc index candle_action296_stratified_16_proof_policies
    with Failure _ ->
      failwith "action296 stratified 16 proof: missing split policy" in
  match policy with
  | Candle_action296_stratified_16_proof_direct ->
      Candle_action296_stratified_16_proof_leaf parent
  | Candle_action296_stratified_16_proof_one_split axis ->
      candle_action296_stratified_16_proof_split axis parent
  | Candle_action296_stratified_16_proof_left_depth_two
      (first_axis,second_axis) ->
      let left,right =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 first_axis parent in
      Candle_action296_stratified_16_proof_split
        (first_axis,
         candle_action296_stratified_16_proof_split second_axis left,
         Candle_action296_stratified_16_proof_leaf right);;

let rec candle_action296_stratified_16_proof_tree_domains = function
  | Candle_action296_stratified_16_proof_leaf domain -> [domain]
  | Candle_action296_stratified_16_proof_split (_,left,right) ->
      candle_action296_stratified_16_proof_tree_domains left @
      candle_action296_stratified_16_proof_tree_domains right;;

let candle_action296_stratified_16_proof_parents =
  map
    (fun index ->
      index,List.nth !candle_action296_leaf_grouping_leaves index)
    candle_action296_stratified_16_proof_indices;;

let _ =
  candle_action296_stratified_16_proof_marker
    "source-preparation" "begin";;
let candle_action296_stratified_16_proof_prepared_ref :
    candle_action296_stratified_16_proof_prepared_six list option ref =
  ref None;;
let _ =
  candle_action296_stratified_16_proof_prepared_ref :=
    Some
      (map
        (fun (index,parent) ->
          let lower,upper =
            candle_action296_leaf_grouping_domain_bounds parent in
          {
            stratified_16_proof_index = index;
            stratified_16_proof_parent = parent;
            stratified_16_proof_prepared =
              candle_q_dim_analytic_jet_prepare_box_six
                candle_action296_plan_prepared.function_term lower upper;
          })
        candle_action296_stratified_16_proof_parents);;
let _ =
  candle_action296_stratified_16_proof_marker
    "source-preparation" "end";;

let candle_action296_stratified_16_proof_prepared () =
  match !candle_action296_stratified_16_proof_prepared_ref with
  | Some prepared -> prepared
  | None -> failwith "action296 stratified 16 proof: missing preparation";;

let _ =
  candle_action296_stratified_16_proof_marker
    "point-plan-compilation" "begin";;
let candle_action296_stratified_16_proof_planned_ref :
    candle_action296_stratified_16_proof_planned_six list option ref =
  ref None;;
let _ =
  candle_action296_stratified_16_proof_planned_ref :=
    Some
      (map
        (fun prepared ->
          {
            stratified_16_proof_planned_index =
              prepared.stratified_16_proof_index;
            stratified_16_proof_planned_parent =
              prepared.stratified_16_proof_parent;
            stratified_16_proof_planned_prepared =
              prepared.stratified_16_proof_prepared;
            stratified_16_proof_plan =
              candle_q_dim_taylor_model_point_plan_six
                prepared.stratified_16_proof_prepared;
          })
        (candle_action296_stratified_16_proof_prepared ()));;
let _ =
  candle_action296_stratified_16_proof_marker
    "point-plan-compilation" "end";;

let candle_action296_stratified_16_proof_planned () =
  match !candle_action296_stratified_16_proof_planned_ref with
  | Some planned -> planned
  | None -> failwith "action296 stratified 16 proof: missing point plans";;

let candle_action296_stratified_16_proof_cell case =
  {
    fixed_algebraic_batch_center_variant =
      case.adaptive_grouping_center_variant;
    fixed_algebraic_batch_lower = case.adaptive_grouping_lower;
    fixed_algebraic_batch_upper = case.adaptive_grouping_upper;
  };;

let _ =
  candle_action296_stratified_16_proof_marker
    "final-cell-preparation" "begin";;
let candle_action296_stratified_16_proof_groups_ref :
    candle_action296_stratified_16_proof_group_six list option ref =
  ref None;;
let _ =
  candle_action296_stratified_16_proof_groups_ref :=
    Some
      (map
        (fun planned ->
          let tree =
            candle_action296_stratified_16_proof_tree
              planned.stratified_16_proof_planned_index
              planned.stratified_16_proof_planned_parent in
          let domains =
            candle_action296_stratified_16_proof_tree_domains tree in
          {
            stratified_16_proof_group_index =
              planned.stratified_16_proof_planned_index;
            stratified_16_proof_group_parent =
              planned.stratified_16_proof_planned_parent;
            stratified_16_proof_group_prepared =
              planned.stratified_16_proof_planned_prepared;
            stratified_16_proof_group_tree = tree;
            stratified_16_proof_group_domains = domains;
            stratified_16_proof_group_cells =
              map
                (fun domain ->
                  candle_action296_stratified_16_proof_cell
                    (candle_action296_adaptive_grouping_case
                      planned.stratified_16_proof_planned_prepared
                      planned.stratified_16_proof_plan domain))
                domains;
          })
        (candle_action296_stratified_16_proof_planned ()));;
let _ =
  candle_action296_stratified_16_proof_marker
    "final-cell-preparation" "end";;

let candle_action296_stratified_16_proof_groups () =
  match !candle_action296_stratified_16_proof_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 stratified 16 proof: missing groups";;

let candle_action296_stratified_16_proof_final_cell_count =
  List.fold_left
    (fun count group ->
      count + length group.stratified_16_proof_group_cells)
    0 (candle_action296_stratified_16_proof_groups ());;

if length (candle_action296_stratified_16_proof_groups ()) <> 16 ||
   candle_action296_stratified_16_proof_final_cell_count <> 26 then
  failwith "action296 stratified 16 proof: adaptive forest shape";;

let _ =
  candle_action296_stratified_16_proof_marker
    "aggregate-proofs" "begin";;
let candle_action296_stratified_16_proof_results_ref :
    candle_q_dim_taylor_model_fixed_algebraic_batch_result_six list
      option ref = ref None;;
let _ =
  candle_action296_stratified_16_proof_results_ref :=
    Some
      (map
        (fun group ->
          candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
            group.stratified_16_proof_group_prepared
            group.stratified_16_proof_group_cells)
        (candle_action296_stratified_16_proof_groups ()));;
let _ =
  candle_action296_stratified_16_proof_marker
    "aggregate-proofs" "end";;

let candle_action296_stratified_16_proof_results () =
  match !candle_action296_stratified_16_proof_results_ref with
  | Some results -> results
  | None -> failwith "action296 stratified 16 proof: missing results";;

let _ =
  candle_action296_stratified_16_proof_marker
    "source-extraction" "begin";;
let candle_action296_stratified_16_proof_source_groups_ref :
    thm list list option ref = ref None;;
let _ =
  candle_action296_stratified_16_proof_source_groups_ref :=
    Some
      (candle_action296_stratified_16_proof_map2
        (fun result group ->
          map
            (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
              result)
            group.stratified_16_proof_group_cells)
        (candle_action296_stratified_16_proof_results ())
        (candle_action296_stratified_16_proof_groups ()));;
let _ =
  candle_action296_stratified_16_proof_marker
    "source-extraction" "end";;

let candle_action296_stratified_16_proof_source_groups () =
  match !candle_action296_stratified_16_proof_source_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 stratified 16 proof: missing sources";;

let candle_action296_stratified_16_proof_live cell source domain =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_stratified_16_proof_aconv_lists
             lower cell.fixed_algebraic_batch_lower &&
           candle_action296_stratified_16_proof_aconv_lists
             upper cell.fixed_algebraic_batch_upper) then
        failwith "action296 stratified 16 proof: unexpected handoff box";
      source)
    domain;;

let rec candle_action296_stratified_16_proof_glue tree live =
  match tree with
  | Candle_action296_stratified_16_proof_leaf _ ->
      (match live with
       | theorem :: remaining -> theorem,remaining
       | [] -> failwith "action296 stratified 16 proof: missing live leaf")
  | Candle_action296_stratified_16_proof_split (axis,left,right) ->
      let left_theorem,after_left =
        candle_action296_stratified_16_proof_glue left live in
      let right_theorem,remaining =
        candle_action296_stratified_16_proof_glue right after_left in
      let glued =
        M_verifier.m_glue_cells_list candle_action296_plan_dimension axis
          left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass
        candle_action296_plan_dimension glued,remaining;;

let _ =
  candle_action296_stratified_16_proof_marker
    "live-handoff-and-glue" "begin";;
let candle_action296_stratified_16_proof_leaf_results_ref :
    (int * thm) list option ref = ref None;;
let _ =
  candle_action296_stratified_16_proof_leaf_results_ref :=
    Some
      (List.flatten
        (candle_action296_stratified_16_proof_map3
          (fun group sources domains ->
            let live =
              candle_action296_stratified_16_proof_map3
                candle_action296_stratified_16_proof_live
                group.stratified_16_proof_group_cells sources domains in
            let theorem,remaining =
              candle_action296_stratified_16_proof_glue
                group.stratified_16_proof_group_tree live in
            if remaining <> [] then
              failwith
                "action296 stratified 16 proof: trailing live leaves";
            [group.stratified_16_proof_group_index,theorem])
          (candle_action296_stratified_16_proof_groups ())
          (candle_action296_stratified_16_proof_source_groups ())
          (map
            (fun group -> group.stratified_16_proof_group_domains)
            (candle_action296_stratified_16_proof_groups ()))));;
let _ =
  candle_action296_stratified_16_proof_marker
    "live-handoff-and-glue" "end";;

let candle_action296_stratified_16_proof_leaf_results () =
  match !candle_action296_stratified_16_proof_leaf_results_ref with
  | Some results -> results
  | None -> failwith "action296 stratified 16 proof: missing leaf results";;

let candle_action296_stratified_16_proof_result_shape theorem =
  M_verifier.dest_m_cell_list_pass (concl theorem);;

let candle_action296_stratified_16_proof_expected_domain domain =
  let actual,_,_ = M_taylor.dest_m_cell_domain (concl domain) in actual;;

let rec candle_action296_stratified_16_proof_validate
    indices results parents =
  match indices,results,parents with
  | [],[],[] -> true
  | expected_index :: remaining_indices,
    (actual_index,theorem) :: remaining_results,
    (parent_index,parent) :: remaining_parents ->
      let functions,proved_domain =
        candle_action296_stratified_16_proof_result_shape theorem in
      actual_index = expected_index &&
      parent_index = expected_index &&
      functions = [candle_action296_plan_prepared.function_term] &&
      aconv proved_domain
        (candle_action296_stratified_16_proof_expected_domain parent) &&
      hyp theorem = [] &&
      candle_action296_stratified_16_proof_validate
        remaining_indices remaining_results remaining_parents
  | _ -> false;;

let candle_action296_stratified_16_proof_digest =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map
          (fun (_,theorem) -> string_of_thm theorem)
          (candle_action296_stratified_16_proof_leaf_results ()))));;

let candle_action296_stratified_16_proof_axioms_after = axioms ();;

if not
     (candle_action296_stratified_16_proof_validate
       candle_action296_stratified_16_proof_indices
       (candle_action296_stratified_16_proof_leaf_results ())
       candle_action296_stratified_16_proof_parents) ||
   candle_action296_stratified_16_proof_digest <>
     "46bb3598d5d6de465bbb33c34a563f68" ||
   length candle_action296_stratified_16_proof_axioms_after <>
     length candle_action296_stratified_16_proof_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_stratified_16_proof_axioms_before)
       candle_action296_stratified_16_proof_axioms_after) then
  failwith "action296 stratified 16 proof: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_STRATIFIED_16_ADAPTIVE_PROOF_RESULT" ^
   " original_leaves=16 final_cells=" ^
   string_of_int candle_action296_stratified_16_proof_final_cell_count ^
   " source_preparations=16 computes=16 theorem_digest=" ^
   candle_action296_stratified_16_proof_digest);;
print_endline
  "CANDLE_CV_ACTION296_STRATIFIED_16_ADAPTIVE_PROOF_OK DEVELOPMENT_NON_RELEASE";;
