(* ========================================================================== *)
(* Complete production sibling 267 with the shared direct case-16594 source. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Certificate search and split discovery are   *)
(* untrusted plan data.  One reflected verdict authenticates all cells and   *)
(* topology before the exact production proposition is reconstructed.        *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_split_scan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare;;
open Candle_cv_analytic_expr_disjunctive_case16597_plan;;
open Candle_cv_analytic_expr_disjunctive_case16597_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_plan_scan;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_split_scan;;

let candle_disjunctive_case16597_prepared =
  candle_disjunctive_case16594_engine_state.family_engine_prepared;;
let candle_disjunctive_case16597_point_plan =
  candle_disjunctive_case16594_engine_state.family_engine_point_plan;;
let candle_disjunctive_case16597_function_term =
  candle_disjunctive_case16594_engine_state.family_engine_function_term;;

if not
     (aconv candle_disjunctive_case16597_function_term
       (List.nth candle_disjunctive_case16597_functions 1)) ||
   candle_disjunctive_case16597_split_scan_unsolved <> [] then
  failwith "case16597 shared complete: prepared plan mismatch";;

type candle_disjunctive_case16597_shape =
  | Candle_disjunctive_case16597_leaf of
      candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six
  | Candle_disjunctive_case16597_node of
      int * candle_disjunctive_case16597_shape *
      candle_disjunctive_case16597_shape;;

let candle_disjunctive_case16597_cell domain =
  let lower,upper = candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16597_point_plan lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_case16597_split_axis leaf =
  let rec find = function
    | [] -> None
    | (candidate,axis)::remaining ->
        if candidate = leaf then Some axis else find remaining in
  find candle_disjunctive_case16597_split_scan_selected;;

let rec candle_disjunctive_case16597_shape_build next_leaf domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "case16597 shared complete: pass selection drift";
      let leaf_index = next_leaf in
      (match candle_disjunctive_case16597_split_axis leaf_index with
       | Some axis ->
           let left_domain,right_domain =
             M_verifier.split_domain 6 6 axis domain in
           Candle_disjunctive_case16597_node
             (axis,
              Candle_disjunctive_case16597_leaf
                (candle_disjunctive_case16597_cell left_domain),
              Candle_disjunctive_case16597_leaf
                (candle_disjunctive_case16597_cell right_domain)),
           leaf_index + 1,2,1
       | None ->
           Candle_disjunctive_case16597_leaf
             (candle_disjunctive_case16597_cell domain),
           leaf_index + 1,1,0)
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16597 shared complete: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left,left_leaves,left_glues =
        candle_disjunctive_case16597_shape_build
          next_leaf left_domain left in
      let right_shape,after_right,right_leaves,right_glues =
        candle_disjunctive_case16597_shape_build
          after_left right_domain right in
      Candle_disjunctive_case16597_node (axis,left_shape,right_shape),
      after_right,left_leaves + right_leaves,1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "case16597 shared complete: monotonicity node"
  | P_result_ref _ ->
      failwith "case16597 shared complete: reference node";;

let rec candle_disjunctive_case16597_cells = function
  | Candle_disjunctive_case16597_leaf cell -> [cell]
  | Candle_disjunctive_case16597_node (_,left,right) ->
      candle_disjunctive_case16597_cells left @
      candle_disjunctive_case16597_cells right;;

type candle_disjunctive_case16597_token =
  | Candle_disjunctive_case16597_token_leaf
  | Candle_disjunctive_case16597_token_glue of int;;

let rec candle_disjunctive_case16597_tokens = function
  | Candle_disjunctive_case16597_leaf _ ->
      [Candle_disjunctive_case16597_token_leaf]
  | Candle_disjunctive_case16597_node (axis,left,right) ->
      candle_disjunctive_case16597_tokens left @
      candle_disjunctive_case16597_tokens right @
      [Candle_disjunctive_case16597_token_glue axis];;

let candle_disjunctive_case16597_encode_token = function
  | Candle_disjunctive_case16597_token_leaf -> `Cexp_num 0`
  | Candle_disjunctive_case16597_token_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let candle_disjunctive_case16597_logical_token = function
  | Candle_disjunctive_case16597_token_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_case16597_token_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let candle_disjunctive_case16597_axioms_before = axioms ();;

let candle_disjunctive_case16597_shape,
    candle_disjunctive_case16597_numerical_cells,
    candle_disjunctive_case16597_glue_nodes =
  let shape,next_leaf,numerical_cells,glue_nodes =
    candle_disjunctive_case16597_shape_build 0
      candle_disjunctive_case16597_root_domain
      candle_disjunctive_case16597_precision_tree in
  if next_leaf <> 1061 || numerical_cells <> 1064 || glue_nodes <> 1063 then
    failwith "case16597 shared complete: compact plan shape drift";
  shape,numerical_cells,glue_nodes;;

let candle_disjunctive_case16597_cell_plan =
  candle_disjunctive_case16597_cells candle_disjunctive_case16597_shape;;
let candle_disjunctive_case16597_token_plan =
  candle_disjunctive_case16597_tokens candle_disjunctive_case16597_shape;;

if length candle_disjunctive_case16597_cell_plan <> 1064 ||
   length candle_disjunctive_case16597_token_plan <> 2127 then
  failwith "case16597 shared complete: flattened plan shape drift";;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16597-shared-certificate-encoding-begin";;
let candle_disjunctive_case16597_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_case16597_cell_plan;;
let candle_disjunctive_case16597_encoded_tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_case16597_encode_token
      candle_disjunctive_case16597_token_plan);;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16597-shared-certificate-encoding-end";;

let candle_disjunctive_case16597_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
     [candle_disjunctive_case16597_prepared.program_representation_term;
      `Cexp_num 6`;candle_disjunctive_case16597_encoded_tokens;
      candle_disjunctive_case16597_encoded_jobs]);;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16597-shared-kernel-compute-begin";;
let candle_disjunctive_case16597_compute =
  candle_q_dim_analytic_jet_compute
    (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
    candle_disjunctive_case16597_call;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16597-shared-kernel-compute-end";;

let candle_disjunctive_case16597_logical_tokens =
  map candle_disjunctive_case16597_logical_token
    candle_disjunctive_case16597_token_plan;;
let candle_disjunctive_case16597_logical_token_term =
  mk_list
    (candle_disjunctive_case16597_logical_tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_case16597_root =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_root_six
    candle_disjunctive_case16597_prepared
    candle_disjunctive_case16597_logical_token_term
    candle_disjunctive_case16597_encoded_tokens
    candle_disjunctive_case16597_encoded_jobs
    candle_disjunctive_case16597_compute;;

let candle_disjunctive_case16597_root_lower,
    candle_disjunctive_case16597_root_upper =
  candle_disjunctive_fixed_outer_domain_bounds
    candle_disjunctive_case16597_root_domain;;
let candle_disjunctive_case16597_expected_root_boxes =
  candle_poly_fixture_q_boxes
    candle_disjunctive_case16597_root_lower
    candle_disjunctive_case16597_root_upper;;

if not
     (aconv candle_disjunctive_case16597_root.variable_complete_root_boxes_term
       candle_disjunctive_case16597_expected_root_boxes) then
  failwith "case16597 shared complete: root box drift";;

let candle_disjunctive_case16597_root_list_pass =
  candle_reflected_nl_source_pass_with
    candle_disjunctive_case16597_function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_shared_aconv_lists
             actual_lower candle_disjunctive_case16597_root_lower &&
           candle_disjunctive_shared_aconv_lists
             actual_upper candle_disjunctive_case16597_root_upper)
      then failwith "case16597 shared complete: root handoff drift";
      candle_disjunctive_case16597_root.variable_complete_root_source_theorem)
    candle_disjunctive_case16597_root_domain;;

let candle_disjunctive_case16597_expanded_general =
  M_verifier_main.normalize_disj_result true
    candle_disjunctive_case16597_functions
    candle_disjunctive_case16597_variable_vector
    candle_disjunctive_case16597_standard
    candle_disjunctive_case16597_domain_subset
    candle_disjunctive_case16597_root_list_pass;;

let candle_disjunctive_case16597_expanded =
  let theorem = SPEC_ALL candle_disjunctive_case16597_expanded_general in
  let bridge =
    TAUT (mk_imp (concl theorem,candle_disjunctive_case16597_converted)) in
  MP bridge theorem;;

let candle_disjunctive_case16597_case_theorem =
  REWRITE_RULE[GSYM candle_disjunctive_case16597_expansion]
    candle_disjunctive_case16597_expanded;;
let candle_disjunctive_case16597_theorem =
  (SPEC_ALL o
   REWRITE_RULE[GSYM candle_disjunctive_case16597_reconstruction])
    candle_disjunctive_case16597_case_theorem;;

let candle_disjunctive_case16597_axioms_after = axioms ();;
let candle_disjunctive_case16597_digest =
  Digest.to_hex
    (Digest.string (string_of_thm candle_disjunctive_case16597_theorem));;

if hyp candle_disjunctive_case16597_root.variable_complete_root_cell_theorem <>
     [] ||
   hyp candle_disjunctive_case16597_root.variable_complete_root_source_theorem <>
     [] ||
   hyp candle_disjunctive_case16597_theorem <> [] ||
   not
     (aconv (concl candle_disjunctive_case16597_theorem)
       candle_disjunctive_case16597_target) ||
   length candle_disjunctive_case16597_axioms_after <>
     length candle_disjunctive_case16597_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_case16597_axioms_before)
       candle_disjunctive_case16597_axioms_after) then
  failwith "case16597 shared complete: final theorem validation failed";;

print_endline
  ("CANDLE_CV_CASE16597_SHARED_COMPLETE_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898 index=267 authenticated_leaves=1061" ^
   " numerical_cells=1064 token_items=2127 reused_direct_programs=2" ^
   " assumptions=0 axiom_growth=0 theorem_digest=" ^
   candle_disjunctive_case16597_digest);;

end;;
