(* ========================================================================== *)
(* Phase decomposition of genuine action-296 center-variant preparation.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Eight distinct exact subboxes are prepared by *)
(* the same operations as                                                     *)
(* candle_q_dim_taylor_model_prepare_point_variant_six, with external phase  *)
(* markers separating hint generation, AST replacement, proof-producing     *)
(* compilation, and reflected program encoding.  The resulting records are   *)
(* accepted by the ordinary proof-producing batch adapter.                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_batch_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_batch_prove;;

let candle_action296_variant_profile_axioms_before = axioms ();;

let candle_action296_variant_profile_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-variant-preparation" ^
     " scope=boxes-8 phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_variant_profile_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_variant_profile_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 variant profile: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 variant profile: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_variant_profile_find left_domain left
  | P_result_mono _ ->
      failwith "action296 variant profile: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 variant profile: unexpected reference node";;

let candle_action296_variant_profile_parent_domain =
  candle_action296_variant_profile_find
    candle_action296_variant_profile_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_variant_profile_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_variant_profile_parent_domain;;

let candle_action296_variant_profile_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_variant_profile_probe_lower,
    candle_action296_variant_profile_probe_upper =
  candle_action296_variant_profile_domain_bounds
    candle_action296_variant_profile_probe_domain;;

let candle_action296_variant_profile_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_variant_profile_probe_lower
    candle_action296_variant_profile_probe_upper;;

let candle_action296_variant_profile_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_variant_profile_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_variant_profile_subdivide remaining
        (List.flatten
          (map (candle_action296_variant_profile_split axis) domains));;

let candle_action296_variant_profile_domains =
  candle_action296_variant_profile_subdivide [1;2;3]
    [candle_action296_variant_profile_probe_domain];;

let candle_action296_variant_profile_bounds =
  map candle_action296_variant_profile_domain_bounds
    candle_action296_variant_profile_domains;;

let candle_action296_variant_profile_variables =
  candle_poly_vector_components
    candle_action296_variant_profile_box_prepared.vector_term 6;;

let rec candle_action296_variant_profile_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_variant_profile_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_action296_variant_profile_check_oracle () =
  candle_action296_variant_profile_marker "legacy-oracle-one" "begin";
  let lower,upper = hd candle_action296_variant_profile_bounds in
  let values = candle_q_point_centers lower upper in
  let oracle_intervals =
    candle_analytic_collect_sqrt_intervals
      (candle_q_point_sqrt_callback_proof
        candle_action296_variant_profile_variables values)
      candle_action296_variant_profile_variables
      candle_action296_variant_profile_box_prepared.source_term and
      fast_intervals =
        candle_analytic_collect_sqrt_intervals
          (candle_q_point_sqrt_callback
            candle_action296_variant_profile_variables values)
          candle_action296_variant_profile_variables
          candle_action296_variant_profile_box_prepared.source_term in
  candle_action296_variant_profile_marker "legacy-oracle-one" "end";
  if not
      (candle_action296_variant_profile_aconv_lists
        oracle_intervals fast_intervals) then
    failwith "action296 variant profile: exact evaluator/oracle mismatch";;

let _ = candle_action296_variant_profile_check_oracle ();;

let candle_action296_variant_profile_variant expression compile_theorem
    representation =
  candle_q_dim_taylor_model_variant_record_six
    candle_action296_variant_profile_box_prepared
    expression compile_theorem representation;;

let candle_action296_variant_profile_cell lower upper variant :
    candle_q_dim_taylor_model_batch_cell_six =
  {
    batch_center_variant = variant;
    batch_lower = lower;
    batch_upper = upper;
  };;

let candle_action296_variant_profile_prepare () =
  candle_action296_variant_profile_marker "sqrt-hints" "begin";
  let intervals =
    map
      (fun (lower,upper) ->
        let values = candle_q_point_centers lower upper in
        candle_analytic_collect_sqrt_intervals
          (candle_q_point_sqrt_callback
            candle_action296_variant_profile_variables values)
          candle_action296_variant_profile_variables
          candle_action296_variant_profile_box_prepared.source_term)
      candle_action296_variant_profile_bounds in
  candle_action296_variant_profile_marker "sqrt-hints" "end";
  candle_action296_variant_profile_marker "ast-replacement" "begin";
  let expressions =
    map
      (fun box_intervals ->
        let expression,remaining =
          candle_analytic_replace_sqrt_intervals box_intervals
            candle_action296_variant_profile_box_prepared.expression_term in
        if remaining <> [] then
          failwith "action296 variant profile: unused intervals";
        expression)
      intervals in
  candle_action296_variant_profile_marker "ast-replacement" "end";
  candle_action296_variant_profile_marker "compile-proof" "begin";
  let compiles =
    map
      (fun expression ->
        REWRITE_CONV
          [candle_analytic_compile_def;candle_poly_compile_def;APPEND]
          (mk_comb (`candle_analytic_compile`,expression)))
      expressions in
  candle_action296_variant_profile_marker "compile-proof" "end";
  candle_action296_variant_profile_marker "program-encoding" "begin";
  let representations =
    map
      (fun compile_theorem ->
        candle_q_dim_analytic_jet_program_encode_conv
          (rand (concl compile_theorem)))
      compiles in
  candle_action296_variant_profile_marker "program-encoding" "end";
  map2
    (fun (lower,upper) (expression,compile_theorem,representation) ->
      candle_action296_variant_profile_cell lower upper
        (candle_action296_variant_profile_variant
          expression compile_theorem representation))
    candle_action296_variant_profile_bounds
    (map2
      (fun expression (compile_theorem,representation) ->
        expression,compile_theorem,representation)
      expressions
      (map2 (fun compile_theorem representation ->
         compile_theorem,representation)
        compiles representations));;

let candle_action296_variant_profile_cells =
  candle_action296_variant_profile_prepare ();;

if length candle_action296_variant_profile_cells <> 8 then
  failwith "action296 variant profile: cell cardinality drift";;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CV_ACTION296_VARIANT_PREPARATION_STAGE event=" ^ event));;

let _ = candle_action296_variant_profile_marker "checked-batch" "begin";;
let candle_action296_variant_profile_result =
  candle_q_dim_taylor_model_batch_prove_six
    candle_action296_variant_profile_box_prepared
    candle_action296_variant_profile_cells;;
let _ = candle_action296_variant_profile_marker "checked-batch" "end";;

let candle_action296_variant_profile_axioms_after = axioms ();;

if length candle_action296_variant_profile_result.batch_cells <> 8 ||
   hyp candle_action296_variant_profile_result.batch_accept_theorem <> [] ||
   length candle_action296_variant_profile_axioms_after <>
     length candle_action296_variant_profile_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_variant_profile_axioms_before)
       candle_action296_variant_profile_axioms_after) then
  failwith "action296 variant profile: final validation failed";;

print_endline
  "CANDLE_CV_ACTION296_VARIANT_PREPARATION_RESULT boxes=8 accepted=8";;
print_endline
  "CANDLE_CV_ACTION296_VARIANT_PREPARATION_OK DEVELOPMENT_NON_RELEASE";;
