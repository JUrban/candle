(* ========================================================================== *)
(* Stable-program/data-only discriminator on genuine action-296 cells.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This benchmark keeps one authenticated encoded *)
(* analytic program and supplies box-specific square-root payloads as untrusted *)
(* data.  It runs the existing reflected numerical checker directly.  As an   *)
(* independent diagnostic, every generated program and box encoding is then   *)
(* compared exactly with the current theorem-producing construction.  No      *)
(* theorem is authorized through the data-only path in this prototype.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;

let candle_action296_stable_data_axioms_before = axioms ();;

let candle_action296_stable_data_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stable-program-data scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_stable_data_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_stable_data_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 stable data: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 stable data: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_stable_data_find left_domain left
  | P_result_mono _ ->
      failwith "action296 stable data: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 stable data: unexpected reference node";;

let candle_action296_stable_data_parent_domain =
  candle_action296_stable_data_find
    candle_action296_stable_data_root_domain
    candle_action296_plan_precision_tree;;

(* The first genuine pass leaf needs one certified split at coordinate four. *)
let candle_action296_stable_data_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_stable_data_parent_domain;;

let candle_action296_stable_data_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_stable_data_probe_lower,
    candle_action296_stable_data_probe_upper =
  candle_action296_stable_data_domain_bounds
    candle_action296_stable_data_probe_domain;;

let candle_action296_stable_data_program =
  candle_action296_plan_prepared.program_representation_term;;

let candle_action296_stable_data_point_plan =
  candle_action296_stable_data_marker
    "shared" "point-plan-compilation" "begin";
  let result =
    candle_q_dim_taylor_model_point_plan_six
      candle_action296_plan_prepared in
  candle_action296_stable_data_marker
    "shared" "point-plan-compilation" "end";
  result;;

let candle_action296_stable_data_variables =
  candle_poly_vector_components
    candle_action296_plan_prepared.vector_term 6;;

let candle_action296_stable_data_box_intervals lower upper =
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  candle_analytic_collect_sqrt_intervals
    (candle_q_box_sqrt_callback
      candle_action296_stable_data_variables bounds)
    candle_action296_stable_data_variables
    candle_action296_plan_prepared.source_term;;

let candle_action296_stable_data_box_intervals_value,
    candle_action296_stable_data_box_patch,
    candle_action296_stable_data_box_program =
  candle_action296_stable_data_marker
    "shared" "whole-box-data-preparation" "begin";
  let intervals =
    candle_action296_stable_data_box_intervals
      candle_action296_stable_data_probe_lower
      candle_action296_stable_data_probe_upper in
  let patch =
    candle_q_dim_stable_program_patch_sqrt_intervals
      intervals candle_action296_stable_data_program in
  let program = patch.stable_program_patch_term in
  candle_action296_stable_data_marker
    "shared" "whole-box-data-preparation" "end";
  intervals,patch,program;;

if length candle_action296_stable_data_box_intervals_value <> 7 ||
   candle_action296_stable_data_box_patch.stable_program_patch_sqrt_slots <>
     7 then
  failwith "action296 stable data: square-root slot count drift";;

let candle_action296_stable_data_expect_failure label operation =
  let failed =
    try let _ = operation () in false with Failure _ -> true in
  if not failed then
    failwith ("action296 stable data: negative test accepted " ^ label);;

let _ =
  candle_action296_stable_data_marker
    "shared" "negative-structure-tests" "begin";;
let _ =
  candle_action296_stable_data_expect_failure "missing-payload"
    (fun () ->
      candle_q_dim_stable_program_patch_sqrt_intervals
        (tl candle_action296_stable_data_box_intervals_value)
        candle_action296_stable_data_program);;
let _ =
  candle_action296_stable_data_expect_failure "extra-payload"
    (fun () ->
      candle_q_dim_stable_program_patch_sqrt_intervals
        (hd candle_action296_stable_data_box_intervals_value ::
         candle_action296_stable_data_box_intervals_value)
        candle_action296_stable_data_program);;
let _ =
  candle_action296_stable_data_expect_failure "malformed-payload"
    (fun () ->
      candle_q_dim_stable_program_patch_sqrt_intervals
        (`0` :: tl candle_action296_stable_data_box_intervals_value)
        candle_action296_stable_data_program);;
let _ =
  candle_action296_stable_data_marker
    "shared" "negative-structure-tests" "end";;

let candle_action296_stable_data_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_stable_data_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_stable_data_subdivide remaining
        (List.flatten
          (map (candle_action296_stable_data_split axis) domains));;

let candle_action296_stable_data_domains_1 =
  [candle_action296_stable_data_probe_domain];;
let candle_action296_stable_data_domains_8 =
  candle_action296_stable_data_subdivide [1;2;3]
    candle_action296_stable_data_domains_1;;
let candle_action296_stable_data_domains_32 =
  candle_action296_stable_data_subdivide [1;2;3;4;5]
    candle_action296_stable_data_domains_1;;

type candle_action296_stable_data_cell = {
  stable_data_lower : term list;
  stable_data_upper : term list;
  stable_data_center_intervals : term list;
  stable_data_center_program : term;
  stable_data_boxes_term : term;
  stable_data_boxes_program : term;
  stable_data_encoded_job : term;
};;

type candle_action296_stable_data_bounds = {
  stable_data_bound_lower : term list;
  stable_data_bound_upper : term list;
};;

let candle_action296_stable_data_bounds domain_th =
  let lower,upper = candle_action296_stable_data_domain_bounds domain_th in
  {stable_data_bound_lower = lower; stable_data_bound_upper = upper};;

let candle_action296_stable_data_cell bounds =
  let lower = bounds.stable_data_bound_lower and
      upper = bounds.stable_data_bound_upper in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_action296_stable_data_point_plan lower upper in
  let center_patch =
    candle_q_dim_stable_program_patch_sqrt_intervals
      center_intervals candle_action296_stable_data_program in
  if center_patch.stable_program_patch_sqrt_slots <> 7 then
    failwith "action296 stable data: center slot count drift";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let encoded_boxes =
    candle_q_dim_stable_program_encode_intervals (dest_list boxes) in
  let encoded_job =
    candle_q_dim_stable_program_cval_pair
      center_patch.stable_program_patch_term encoded_boxes in
  {stable_data_lower = lower;
   stable_data_upper = upper;
   stable_data_center_intervals = center_intervals;
   stable_data_center_program = center_patch.stable_program_patch_term;
   stable_data_boxes_term = boxes;
   stable_data_boxes_program = encoded_boxes;
   stable_data_encoded_job = encoded_job};;

let candle_action296_stable_data_prepare_bounds scope domains =
  candle_action296_stable_data_marker
    scope "per-box-domain-normalization" "begin";
  let bounds = map candle_action296_stable_data_bounds domains in
  candle_action296_stable_data_marker
    scope "per-box-domain-normalization" "end";
  bounds;;

let candle_action296_stable_data_prepare scope bounds =
  candle_action296_stable_data_marker
    scope "per-box-certificate-data" "begin";
  let cells = map candle_action296_stable_data_cell bounds in
  candle_action296_stable_data_marker
    scope "per-box-certificate-data" "end";
  cells;;

let candle_action296_stable_data_bounds_1 =
  candle_action296_stable_data_prepare_bounds
    "boxes-1" candle_action296_stable_data_domains_1;;
let candle_action296_stable_data_bounds_8 =
  candle_action296_stable_data_prepare_bounds
    "boxes-8" candle_action296_stable_data_domains_8;;
let candle_action296_stable_data_bounds_32 =
  candle_action296_stable_data_prepare_bounds
    "boxes-32" candle_action296_stable_data_domains_32;;

let candle_action296_stable_data_cells_1 =
  candle_action296_stable_data_prepare
    "boxes-1" candle_action296_stable_data_bounds_1;;
let candle_action296_stable_data_cells_8 =
  candle_action296_stable_data_prepare
    "boxes-8" candle_action296_stable_data_bounds_8;;
let candle_action296_stable_data_cells_32 =
  candle_action296_stable_data_prepare
    "boxes-32" candle_action296_stable_data_bounds_32;;

if length candle_action296_stable_data_cells_1 <> 1 ||
   length candle_action296_stable_data_cells_8 <> 8 ||
   length candle_action296_stable_data_cells_32 <> 32 then
  failwith "action296 stable data: subdivision cardinality drift";;

let candle_action296_stable_data_run scope cells =
  let encoded_jobs =
    candle_q_dim_stable_program_cval_list
      (map (fun cell -> cell.stable_data_encoded_job) cells) in
  let call =
    list_mk_comb
      (`candle_cv_fsa_batch_check`,
       [candle_action296_stable_data_box_program;encoded_jobs]) in
  candle_action296_stable_data_marker scope "kernel-compute" "begin";
  let result =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsa_batch_compute_eqs call in
  candle_action296_stable_data_marker scope "kernel-compute" "end";
  if hyp result <> [] || not (aconv (rand (concl result)) `Cexp_num 1`) then
    failwith "action296 stable data: reflected batch rejected";
  result;;

let candle_action296_stable_data_result_1 =
  candle_action296_stable_data_run
    "boxes-1" candle_action296_stable_data_cells_1;;
let candle_action296_stable_data_result_8 =
  candle_action296_stable_data_run
    "boxes-8" candle_action296_stable_data_cells_8;;
let candle_action296_stable_data_result_32 =
  candle_action296_stable_data_run
    "boxes-32" candle_action296_stable_data_cells_32;;

let candle_action296_stable_data_oracle_box =
  (* Validate the candidate data against the existing theorem-producing path. *)
  candle_action296_stable_data_marker
    "oracle" "whole-box-source-preparation" "begin";
  let result =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term
      candle_action296_stable_data_probe_lower
      candle_action296_stable_data_probe_upper in
  candle_action296_stable_data_marker
    "oracle" "whole-box-source-preparation" "end";
  result;;

if not
    (aconv candle_action296_stable_data_box_program
      candle_action296_stable_data_oracle_box.program_representation_term) then
  failwith "action296 stable data: whole-box program differs from oracle";;

let candle_action296_stable_data_validate_cell cell =
  let variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_stable_data_oracle_box
      candle_action296_stable_data_point_plan
      cell.stable_data_lower cell.stable_data_upper in
  if not
      (aconv cell.stable_data_center_program
        variant.variant_program_representation_term) then
    failwith "action296 stable data: center program differs from oracle";
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv
      cell.stable_data_boxes_term in
  if not
      (aconv cell.stable_data_boxes_program
        (rand (concl boxes_representation))) then
    failwith "action296 stable data: box encoding differs from oracle";;

let candle_action296_stable_data_validate scope cells =
  candle_action296_stable_data_marker
    scope "trusted-oracle-validation" "begin";
  do_list candle_action296_stable_data_validate_cell cells;
  candle_action296_stable_data_marker
    scope "trusted-oracle-validation" "end";;

let _ =
  candle_action296_stable_data_validate
    "boxes-1" candle_action296_stable_data_cells_1;;
let _ =
  candle_action296_stable_data_validate
    "boxes-8" candle_action296_stable_data_cells_8;;
let _ =
  candle_action296_stable_data_validate
    "boxes-32" candle_action296_stable_data_cells_32;;

let candle_action296_stable_data_axioms_after = axioms ();;

if length candle_action296_stable_data_axioms_after <>
     length candle_action296_stable_data_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_stable_data_axioms_before)
       candle_action296_stable_data_axioms_after) then
  failwith "action296 stable data: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_STABLE_PROGRAM_DATA_RESULT boxes=1,8,32" ^
   " accepted=41 oracle_equalities=41 sqrt_slots=7" ^
   " stable_programs=1 theorem_authority=none");;
print_endline
  "CANDLE_CV_ACTION296_STABLE_PROGRAM_DATA_OK DEVELOPMENT_NON_RELEASE";;
