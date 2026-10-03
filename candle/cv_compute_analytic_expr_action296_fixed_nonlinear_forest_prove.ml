(* ========================================================================== *)
(* Proved fixed-nonlinear adapter for genuine action-296 leaf forests.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Split plans are untrusted data.  Every final  *)
(* cell is checked independently, transported to its exact Flyspeck domain,  *)
(* and glued through the existing kernel theorems.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_action296_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_certified_prove.ml";;

module Candle_cv_action296_fixed_nonlinear_forest_prove = struct

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_prove;;
open Candle_cv_action296_forest_plan;;

type candle_action296_fixed_nonlinear_forest_result = {
  fixed_nonlinear_forest_result_original_roots : int;
  fixed_nonlinear_forest_result_final_cells : int;
  fixed_nonlinear_forest_result_theorems : (int * thm) list;
  fixed_nonlinear_forest_result_digest : string;
};;

let candle_action296_fixed_nonlinear_forest_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-nonlinear-forest-proof" ^
     " scope=forest phase=" ^ phase ^ " event=" ^ event);;

let rec candle_action296_fixed_nonlinear_forest_strict_roots previous =
  function
  | [] -> true
  | (index,_) :: remaining ->
      index > previous && index >= 0 &&
      index < length !candle_action296_leaf_grouping_leaves &&
      candle_action296_fixed_nonlinear_forest_strict_roots index remaining;;

let rec candle_action296_fixed_nonlinear_forest_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_fixed_nonlinear_forest_aconv_lists
        left_tail right_tail
  | _ -> false;;

let rec candle_action296_fixed_nonlinear_forest_glue tree live =
  match tree with
  | Candle_action296_forest_tree_leaf _ ->
      (match live with
       | theorem :: remaining -> theorem,remaining
       | [] ->
           failwith "action296 fixed nonlinear forest: missing live leaf")
  | Candle_action296_forest_tree_split (axis,left,right) ->
      let left_theorem,after_left =
        candle_action296_fixed_nonlinear_forest_glue left live in
      let right_theorem,remaining =
        candle_action296_fixed_nonlinear_forest_glue right after_left in
      let glued =
        M_verifier.m_glue_cells_list candle_action296_plan_dimension axis
          left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass
        candle_action296_plan_dimension glued,remaining;;

let candle_action296_fixed_nonlinear_forest_expected_domain domain =
  let actual,_,_ = M_taylor.dest_m_cell_domain (concl domain) in actual;;

let candle_action296_fixed_nonlinear_forest_validate_result
    index parent theorem =
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl theorem) in
  functions = [candle_action296_plan_prepared.function_term] &&
  aconv proved_domain
    (candle_action296_fixed_nonlinear_forest_expected_domain parent) &&
  hyp theorem = [];;

(* Point-program structure depends only on the authenticated expression and  *)
(* variable order, so this compilation is shared by every root and cell.     *)

let candle_action296_fixed_nonlinear_forest_point_plan =
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      "shared-point-plan-compilation" "begin" in
  let plan =
    candle_q_dim_taylor_model_point_plan_six candle_action296_plan_prepared in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      "shared-point-plan-compilation" "end" in
  plan;;

let candle_action296_fixed_nonlinear_forest_prove_cell
    prepared domain =
  let lower,upper = candle_action296_leaf_grouping_domain_bounds domain in
  let variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      prepared candle_action296_fixed_nonlinear_forest_point_plan
      lower upper in
  let source =
    candle_q_dim_taylor_model_fixed_nonlinear_certified_prove_box_variant_six
      variant prepared lower upper in
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_action296_fixed_nonlinear_forest_aconv_lists
             actual_lower lower &&
           candle_action296_fixed_nonlinear_forest_aconv_lists
             actual_upper upper) then
        failwith
          "action296 fixed nonlinear forest: unexpected handoff box";
      source)
    domain;;

let candle_action296_fixed_nonlinear_forest_prove_one index plan_data =
  let phase = "root-" ^ string_of_int index in
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-source-preparation") "begin" in
  let prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term lower upper in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-source-preparation") "end" in
  let tree = candle_action296_forest_build_tree parent plan_data in
  let domains = candle_action296_forest_tree_domains tree in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-cell-proofs") "begin" in
  let live =
    map
      (candle_action296_fixed_nonlinear_forest_prove_cell prepared)
      domains in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-cell-proofs") "end" in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-glue") "begin" in
  let theorem,remaining =
    candle_action296_fixed_nonlinear_forest_glue tree live in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      (phase ^ "-glue") "end" in
  if remaining <> [] ||
     not
       (candle_action296_fixed_nonlinear_forest_validate_result
         index parent theorem) then
    failwith
      ("action296 fixed nonlinear forest: invalid root " ^
       string_of_int index);
  index,theorem,length domains;;

let candle_action296_fixed_nonlinear_forest_prove_sequential
    label roots expected_final_cells expected_digest =
  if roots = [] ||
     not
       (candle_action296_fixed_nonlinear_forest_strict_roots (-1) roots) then
    failwith "action296 fixed nonlinear forest: invalid root plan";
  let axioms_before = axioms () in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      "sequential-forest" "begin" in
  let completed =
    map
      (fun (index,plan_data) ->
        candle_action296_fixed_nonlinear_forest_prove_one index plan_data)
      roots in
  let _ =
    candle_action296_fixed_nonlinear_forest_marker
      "sequential-forest" "end" in
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
      ("action296 fixed nonlinear forest: final validation failed for " ^
       label);
  {
    fixed_nonlinear_forest_result_original_roots = length roots;
    fixed_nonlinear_forest_result_final_cells = final_cell_count;
    fixed_nonlinear_forest_result_theorems = root_results;
    fixed_nonlinear_forest_result_digest = digest;
  };;

end;;
