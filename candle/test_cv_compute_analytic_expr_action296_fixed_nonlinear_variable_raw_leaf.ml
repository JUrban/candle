(* ========================================================================== *)
(* Genuine action-296 two-cell test of the canonical raw nonlinear boundary.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;

let candle_action296_fixed_nonlinear_variable_raw_axioms_before = axioms ();;

let candle_action296_fixed_nonlinear_variable_raw_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_fixed_nonlinear_variable_raw_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "fixed nonlinear variable raw: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "fixed nonlinear variable raw: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fixed_nonlinear_variable_raw_find left_domain left
  | P_result_mono _ ->
      failwith "fixed nonlinear variable raw: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "fixed nonlinear variable raw: unexpected reference node";;

let candle_action296_fixed_nonlinear_variable_raw_parent_domain =
  candle_action296_fixed_nonlinear_variable_raw_find
    candle_action296_fixed_nonlinear_variable_raw_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_fixed_nonlinear_variable_raw_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_fixed_nonlinear_variable_raw_left_domain,
    candle_action296_fixed_nonlinear_variable_raw_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_fixed_nonlinear_variable_raw_parent_domain;;

let candle_action296_fixed_nonlinear_variable_raw_parent_lower,
    candle_action296_fixed_nonlinear_variable_raw_parent_upper =
  candle_action296_fixed_nonlinear_variable_raw_domain_bounds
    candle_action296_fixed_nonlinear_variable_raw_parent_domain;;

let candle_action296_fixed_nonlinear_variable_raw_variables =
  candle_poly_vector_components candle_action296_plan_prepared.vector_term 6;;

let candle_action296_fixed_nonlinear_variable_raw_box_intervals =
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      candle_action296_fixed_nonlinear_variable_raw_parent_lower
      candle_action296_fixed_nonlinear_variable_raw_parent_upper in
  candle_analytic_collect_sqrt_intervals
    (candle_q_box_sqrt_callback
      candle_action296_fixed_nonlinear_variable_raw_variables bounds)
    candle_action296_fixed_nonlinear_variable_raw_variables
    candle_action296_plan_prepared.source_term;;

let candle_action296_fixed_nonlinear_variable_raw_point_plan =
  candle_q_dim_taylor_model_point_plan_six candle_action296_plan_prepared;;

let candle_action296_fixed_nonlinear_variable_raw_cell domain_th =
  let lower,upper =
    candle_action296_fixed_nonlinear_variable_raw_domain_bounds domain_th in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_action296_fixed_nonlinear_variable_raw_point_plan lower upper in
  {variable_batch_box_intervals =
     candle_action296_fixed_nonlinear_variable_raw_box_intervals;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_action296_fixed_nonlinear_variable_raw_cells =
  map candle_action296_fixed_nonlinear_variable_raw_cell
    [candle_action296_fixed_nonlinear_variable_raw_left_domain;
     candle_action296_fixed_nonlinear_variable_raw_right_domain];;

let candle_action296_fixed_nonlinear_variable_raw_result =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
    candle_action296_plan_prepared
    candle_action296_fixed_nonlinear_variable_raw_cells;;

let candle_action296_fixed_nonlinear_variable_raw_axioms_after = axioms ();;

if hyp
     candle_action296_fixed_nonlinear_variable_raw_result.
       fixed_nonlinear_variable_raw_representation_theorem <> [] ||
   hyp
     candle_action296_fixed_nonlinear_variable_raw_result.
       fixed_nonlinear_variable_raw_accept_theorem <> [] ||
   length candle_action296_fixed_nonlinear_variable_raw_axioms_after <>
     length candle_action296_fixed_nonlinear_variable_raw_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_fixed_nonlinear_variable_raw_axioms_before)
       candle_action296_fixed_nonlinear_variable_raw_axioms_after) then
  failwith "fixed nonlinear variable raw: validation failed";;

print_endline
  "CANDLE_CV_ACTION296_FIXED_NONLINEAR_VARIABLE_RAW_LEAF_RESULT cells=2 source_preparations=0 computes=1 assumptions=0 axiom_growth=0";;
print_endline
  "CANDLE_CV_ACTION296_FIXED_NONLINEAR_VARIABLE_RAW_LEAF_OK DEVELOPMENT_NON_RELEASE";;
