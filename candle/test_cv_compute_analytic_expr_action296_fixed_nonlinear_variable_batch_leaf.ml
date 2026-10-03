(* ========================================================================== *)
(* Complete stable-source/fixed-nonlinear proof of one genuine action-296     *)
(* leaf.  The two changing certificates are ordinary checked job data.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_prove;;

let candle_action296_fixed_nonlinear_variable_leaf_axioms_before = axioms ();;

let candle_action296_fixed_nonlinear_variable_leaf_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-nonlinear-variable-leaf" ^
     " scope=leaf phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      if event = "fixed-nonlinear-variable-batch-preparation-begin" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "proof-input-preparation" "begin"
      else if event = "fixed-nonlinear-variable-batch-preparation-end" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "proof-input-preparation" "end"
      else if event = "fixed-nonlinear-variable-batch-compute-begin" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "kernel-compute" "begin"
      else if event = "fixed-nonlinear-variable-batch-compute-end" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "kernel-compute" "end"
      else if event = "fixed-nonlinear-variable-batch-handoff-begin" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "compact-verdict-handoff" "begin"
      else if event = "fixed-nonlinear-variable-batch-handoff-end" then
        candle_action296_fixed_nonlinear_variable_leaf_marker
          "compact-verdict-handoff" "end"
      else ());;

let candle_action296_fixed_nonlinear_variable_leaf_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_fixed_nonlinear_variable_leaf_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "fixed nonlinear variable leaf: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "fixed nonlinear variable leaf: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fixed_nonlinear_variable_leaf_find left_domain left
  | P_result_mono _ ->
      failwith "fixed nonlinear variable leaf: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "fixed nonlinear variable leaf: unexpected reference node";;

let candle_action296_fixed_nonlinear_variable_leaf_parent_domain =
  candle_action296_fixed_nonlinear_variable_leaf_find
    candle_action296_fixed_nonlinear_variable_leaf_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_fixed_nonlinear_variable_leaf_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_fixed_nonlinear_variable_leaf_parent_lower,
    candle_action296_fixed_nonlinear_variable_leaf_parent_upper =
  candle_action296_fixed_nonlinear_variable_leaf_domain_bounds
    candle_action296_fixed_nonlinear_variable_leaf_parent_domain;;

let candle_action296_fixed_nonlinear_variable_leaf_left_domain,
    candle_action296_fixed_nonlinear_variable_leaf_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_fixed_nonlinear_variable_leaf_parent_domain;;

let candle_action296_fixed_nonlinear_variable_leaf_variables =
  candle_poly_vector_components candle_action296_plan_prepared.vector_term 6;;

let candle_action296_fixed_nonlinear_variable_leaf_box_intervals =
  candle_action296_fixed_nonlinear_variable_leaf_marker
    "certificate-data" "begin";
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      candle_action296_fixed_nonlinear_variable_leaf_parent_lower
      candle_action296_fixed_nonlinear_variable_leaf_parent_upper in
  let intervals =
    candle_analytic_collect_sqrt_intervals
      (candle_q_box_sqrt_callback
        candle_action296_fixed_nonlinear_variable_leaf_variables bounds)
      candle_action296_fixed_nonlinear_variable_leaf_variables
      candle_action296_plan_prepared.source_term in
  candle_action296_fixed_nonlinear_variable_leaf_marker
    "certificate-data" "end";
  intervals;;

let candle_action296_fixed_nonlinear_variable_leaf_point_plan =
  candle_q_dim_taylor_model_point_plan_six candle_action296_plan_prepared;;

let candle_action296_fixed_nonlinear_variable_leaf_cell domain_th =
  let lower,upper =
    candle_action296_fixed_nonlinear_variable_leaf_domain_bounds domain_th in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_action296_fixed_nonlinear_variable_leaf_point_plan lower upper in
  {variable_batch_box_intervals =
     candle_action296_fixed_nonlinear_variable_leaf_box_intervals;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_action296_fixed_nonlinear_variable_leaf_cells =
  map candle_action296_fixed_nonlinear_variable_leaf_cell
    [candle_action296_fixed_nonlinear_variable_leaf_left_domain;
     candle_action296_fixed_nonlinear_variable_leaf_right_domain];;

let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker "batch" "begin";;
let candle_action296_fixed_nonlinear_variable_leaf_result =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_prove_six
    candle_action296_plan_prepared
    candle_action296_fixed_nonlinear_variable_leaf_cells;;
let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker "batch" "end";;

let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker
    "source-theorem-extraction" "begin";;
let candle_action296_fixed_nonlinear_variable_leaf_sources =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_batch_sources_six
    candle_action296_fixed_nonlinear_variable_leaf_result;;
let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker
    "source-theorem-extraction" "end";;

let rec candle_action296_fixed_nonlinear_variable_leaf_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_fixed_nonlinear_variable_leaf_aconv_lists
        left_tail right_tail
  | _ -> false;;

let candle_action296_fixed_nonlinear_variable_leaf_live source cell domain =
  let expected = cell.variable_batch_stable_cell in
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_fixed_nonlinear_variable_leaf_aconv_lists
             lower expected.stable_batch_lower &&
           candle_action296_fixed_nonlinear_variable_leaf_aconv_lists
             upper expected.stable_batch_upper) then
        failwith "fixed nonlinear variable leaf: unexpected handoff box";
      source)
    domain;;

let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker "live-handoff" "begin";;
let candle_action296_fixed_nonlinear_variable_leaf_live_sources =
  match candle_action296_fixed_nonlinear_variable_leaf_sources,
        candle_action296_fixed_nonlinear_variable_leaf_cells with
  | [left_source;right_source],[left_cell;right_cell] ->
      [candle_action296_fixed_nonlinear_variable_leaf_live
        left_source left_cell
        candle_action296_fixed_nonlinear_variable_leaf_left_domain;
       candle_action296_fixed_nonlinear_variable_leaf_live
        right_source right_cell
        candle_action296_fixed_nonlinear_variable_leaf_right_domain]
  | _ -> failwith "fixed nonlinear variable leaf: source cardinality";;
let _ =
  candle_action296_fixed_nonlinear_variable_leaf_marker "live-handoff" "end";;

let candle_action296_fixed_nonlinear_variable_leaf_theorem =
  match candle_action296_fixed_nonlinear_variable_leaf_live_sources with
  | [left;right] ->
      M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
        (M_verifier.m_glue_cells_list
          candle_action296_plan_dimension 4 left right)
  | _ -> failwith "fixed nonlinear variable leaf: result cardinality";;

let candle_action296_fixed_nonlinear_variable_leaf_functions,
    candle_action296_fixed_nonlinear_variable_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_fixed_nonlinear_variable_leaf_theorem);;

let candle_action296_fixed_nonlinear_variable_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_fixed_nonlinear_variable_leaf_parent_domain);;

let candle_action296_fixed_nonlinear_variable_leaf_theorem_md5 =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_action296_fixed_nonlinear_variable_leaf_theorem));;

let candle_action296_fixed_nonlinear_variable_leaf_axioms_after = axioms ();;

if length candle_action296_fixed_nonlinear_variable_leaf_sources <> 2 ||
   candle_action296_fixed_nonlinear_variable_leaf_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_fixed_nonlinear_variable_leaf_proved_domain
       candle_action296_fixed_nonlinear_variable_leaf_expected_domain) ||
   hyp candle_action296_fixed_nonlinear_variable_leaf_theorem <> [] ||
   candle_action296_fixed_nonlinear_variable_leaf_theorem_md5 <>
     "926f44ab8d5f2303064fe5788cead588" ||
   length candle_action296_fixed_nonlinear_variable_leaf_axioms_after <>
     length candle_action296_fixed_nonlinear_variable_leaf_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_fixed_nonlinear_variable_leaf_axioms_before)
       candle_action296_fixed_nonlinear_variable_leaf_axioms_after) then
  failwith "fixed nonlinear variable leaf: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_NONLINEAR_VARIABLE_LEAF_RESULT cells=2" ^
   " source_preparations=0 computes=1 theorem_md5=" ^
   candle_action296_fixed_nonlinear_variable_leaf_theorem_md5);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_NONLINEAR_VARIABLE_LEAF_OK DEVELOPMENT_NON_RELEASE";;
