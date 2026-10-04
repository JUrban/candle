(* ========================================================================== *)
(* Complete production sibling 149 with the shared direct case-16594 source. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The authenticated precision tree and seven   *)
(* bounded retry splits are untrusted plan data.  The direct 167-instruction *)
(* source program, all 795 numerical cells, the 1,589-item topology, and the *)
(* exact Flyspeck theorem are checked by the general reflected interfaces.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16479_direct_leaf_grouping.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16479_shared_complete = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16479_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16479_plan;;
open Candle_cv_analytic_expr_disjunctive_case16479_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove;;

let rec candle_disjunctive_case16479_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_case16479_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_case16479_prepared =
  candle_disjunctive_case16594_engine_state.family_engine_prepared;;
let candle_disjunctive_case16479_point_plan =
  candle_disjunctive_case16594_engine_state.family_engine_point_plan;;
let candle_disjunctive_case16479_function_term =
  candle_disjunctive_case16594_engine_state.family_engine_function_term;;

if not
     (aconv candle_disjunctive_case16479_function_term
       (List.nth candle_disjunctive_case16479_functions 1)) then
  failwith "case16479 shared complete: prepared source mismatch";;

type candle_disjunctive_case16479_shape =
  | Candle_disjunctive_case16479_leaf of
      candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six
  | Candle_disjunctive_case16479_node of
      int * candle_disjunctive_case16479_shape *
      candle_disjunctive_case16479_shape;;

let candle_disjunctive_case16479_split_leaves =
  [387;420;422;424;446;536;688];;

let candle_disjunctive_case16479_cell domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16479_point_plan lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let rec candle_disjunctive_case16479_shape_build next_leaf domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "case16479 shared complete: pass selection drift";
      let leaf_index = next_leaf in
      if List.mem leaf_index candle_disjunctive_case16479_split_leaves then
        let left_domain,right_domain =
          M_verifier.split_domain 6 6 1 domain in
        Candle_disjunctive_case16479_node
          (1,
           Candle_disjunctive_case16479_leaf
             (candle_disjunctive_case16479_cell left_domain),
           Candle_disjunctive_case16479_leaf
             (candle_disjunctive_case16479_cell right_domain)),
        leaf_index + 1,2,1
      else
        Candle_disjunctive_case16479_leaf
          (candle_disjunctive_case16479_cell domain),
        leaf_index + 1,1,0
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16479 shared complete: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left,left_leaves,left_glues =
        candle_disjunctive_case16479_shape_build
          next_leaf left_domain left in
      let right_shape,after_right,right_leaves,right_glues =
        candle_disjunctive_case16479_shape_build
          after_left right_domain right in
      Candle_disjunctive_case16479_node (axis,left_shape,right_shape),
      after_right,left_leaves + right_leaves,1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "case16479 shared complete: monotonicity node"
  | P_result_ref _ ->
      failwith "case16479 shared complete: reference node";;

let rec candle_disjunctive_case16479_cells = function
  | Candle_disjunctive_case16479_leaf cell -> [cell]
  | Candle_disjunctive_case16479_node (_,left,right) ->
      candle_disjunctive_case16479_cells left @
      candle_disjunctive_case16479_cells right;;

type candle_disjunctive_case16479_token =
  | Candle_disjunctive_case16479_token_leaf
  | Candle_disjunctive_case16479_token_glue of int;;

let rec candle_disjunctive_case16479_tokens = function
  | Candle_disjunctive_case16479_leaf _ ->
      [Candle_disjunctive_case16479_token_leaf]
  | Candle_disjunctive_case16479_node (axis,left,right) ->
      candle_disjunctive_case16479_tokens left @
      candle_disjunctive_case16479_tokens right @
      [Candle_disjunctive_case16479_token_glue axis];;

let candle_disjunctive_case16479_encode_token = function
  | Candle_disjunctive_case16479_token_leaf -> `Cexp_num 0`
  | Candle_disjunctive_case16479_token_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let candle_disjunctive_case16479_logical_token = function
  | Candle_disjunctive_case16479_token_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_case16479_token_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let candle_disjunctive_case16479_axioms_before = axioms ();;

let candle_disjunctive_case16479_shape,
    candle_disjunctive_case16479_numerical_cells,
    candle_disjunctive_case16479_glue_nodes =
  let shape,next_leaf,numerical_cells,glue_nodes =
    candle_disjunctive_case16479_shape_build 0
      candle_disjunctive_case16479_root_domain
      candle_disjunctive_case16479_precision_tree in
  if next_leaf <> 788 || numerical_cells <> 795 || glue_nodes <> 794 then
    failwith "case16479 shared complete: compact plan shape drift";
  shape,numerical_cells,glue_nodes;;

let candle_disjunctive_case16479_cell_plan =
  candle_disjunctive_case16479_cells candle_disjunctive_case16479_shape;;
let candle_disjunctive_case16479_token_plan =
  candle_disjunctive_case16479_tokens candle_disjunctive_case16479_shape;;

if length candle_disjunctive_case16479_cell_plan <> 795 ||
   length candle_disjunctive_case16479_token_plan <> 1589 then
  failwith "case16479 shared complete: flattened plan shape drift";;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16479-shared-certificate-encoding-begin";;
let candle_disjunctive_case16479_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_case16479_cell_plan;;
let candle_disjunctive_case16479_encoded_tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_case16479_encode_token
      candle_disjunctive_case16479_token_plan);;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16479-shared-certificate-encoding-end";;

let candle_disjunctive_case16479_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
     [candle_disjunctive_case16479_prepared.program_representation_term;
      `Cexp_num 6`;candle_disjunctive_case16479_encoded_tokens;
      candle_disjunctive_case16479_encoded_jobs]);;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16479-shared-kernel-compute-begin";;
let candle_disjunctive_case16479_compute =
  candle_q_dim_analytic_jet_compute
    (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
    candle_disjunctive_case16479_call;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "case16479-shared-kernel-compute-end";;

let candle_disjunctive_case16479_logical_tokens =
  map candle_disjunctive_case16479_logical_token
    candle_disjunctive_case16479_token_plan;;
let candle_disjunctive_case16479_logical_token_term =
  mk_list
    (candle_disjunctive_case16479_logical_tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_case16479_root =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_root_six
    candle_disjunctive_case16479_prepared
    candle_disjunctive_case16479_logical_token_term
    candle_disjunctive_case16479_encoded_tokens
    candle_disjunctive_case16479_encoded_jobs
    candle_disjunctive_case16479_compute;;

let candle_disjunctive_case16479_root_lower,
    candle_disjunctive_case16479_root_upper =
  candle_disjunctive_fixed_outer_domain_bounds
    candle_disjunctive_case16479_root_domain;;
let candle_disjunctive_case16479_expected_root_boxes =
  candle_poly_fixture_q_boxes
    candle_disjunctive_case16479_root_lower
    candle_disjunctive_case16479_root_upper;;

if not
     (aconv candle_disjunctive_case16479_root.variable_complete_root_boxes_term
       candle_disjunctive_case16479_expected_root_boxes) then
  failwith "case16479 shared complete: root box drift";;

let candle_disjunctive_case16479_root_list_pass =
  candle_reflected_nl_source_pass_with
    candle_disjunctive_case16479_function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_case16479_aconv_lists
             actual_lower candle_disjunctive_case16479_root_lower &&
           candle_disjunctive_case16479_aconv_lists
             actual_upper candle_disjunctive_case16479_root_upper)
      then failwith "case16479 shared complete: root handoff drift";
      candle_disjunctive_case16479_root.variable_complete_root_source_theorem)
    candle_disjunctive_case16479_root_domain;;

let candle_disjunctive_case16479_expanded_general =
  M_verifier_main.normalize_disj_result true
    candle_disjunctive_case16479_functions
    candle_disjunctive_case16479_variable_vector
    candle_disjunctive_case16479_standard
    candle_disjunctive_case16479_domain_subset
    candle_disjunctive_case16479_root_list_pass;;

let candle_disjunctive_case16479_expanded =
  let theorem = SPEC_ALL candle_disjunctive_case16479_expanded_general in
  let bridge =
    TAUT (mk_imp (concl theorem,candle_disjunctive_case16479_converted)) in
  MP bridge theorem;;

let candle_disjunctive_case16479_case_theorem =
  REWRITE_RULE[GSYM candle_disjunctive_case16479_expansion]
    candle_disjunctive_case16479_expanded;;
let candle_disjunctive_case16479_theorem =
  (SPEC_ALL o
   REWRITE_RULE[GSYM candle_disjunctive_case16479_reconstruction])
    candle_disjunctive_case16479_case_theorem;;

let candle_disjunctive_case16479_axioms_after = axioms ();;
let candle_disjunctive_case16479_digest =
  Digest.to_hex
    (Digest.string (string_of_thm candle_disjunctive_case16479_theorem));;

if hyp candle_disjunctive_case16479_root.variable_complete_root_cell_theorem <>
     [] ||
   hyp candle_disjunctive_case16479_root.variable_complete_root_source_theorem <>
     [] ||
   hyp candle_disjunctive_case16479_theorem <> [] ||
   not
     (aconv (concl candle_disjunctive_case16479_theorem)
       candle_disjunctive_case16479_target) ||
   candle_disjunctive_case16479_digest <>
     "0ab4e6a6c5a65fcce2d819532a7e7eee" ||
   length candle_disjunctive_case16479_axioms_after <>
     length candle_disjunctive_case16479_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_case16479_axioms_before)
       candle_disjunctive_case16479_axioms_after) then
  failwith "case16479 shared complete: final theorem validation failed";;

print_endline
  ("CANDLE_CV_CASE16479_SHARED_COMPLETE_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898 index=149 authenticated_leaves=788" ^
   " numerical_cells=795 token_items=1589 reused_direct_programs=2" ^
   " assumptions=0 axiom_growth=0 theorem_digest=" ^
   candle_disjunctive_case16479_digest);;

end;;
