(* ========================================================================== *)
(* Amortized 1/8/64-box scaling probe for a genuine action-296 cell.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source expression and whole-box analytic  *)
(* certificate are prepared once.  Exact, distinct subdivisions of one cell *)
(* that already passed the genuine Flyspeck certificate are then prepared    *)
(* and checked in one reflected batch per size.  Flushed phase markers are    *)
(* intended for the external certificate_phase_profile.py observer: Candle's *)
(* selected runtime deliberately has no wall clock.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_batch_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_batch;;
open Candle_cv_analytic_expr_taylor_model_batch_prove;;

let candle_action296_batch_scaling_axioms_before = axioms ();;

let candle_action296_batch_scaling_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-batch-scaling scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_batch_scaling_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_batch_scaling_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 batch scaling: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 batch scaling: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_batch_scaling_find left_domain left
  | P_result_mono _ ->
      failwith "action296 batch scaling: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 batch scaling: unexpected reference node";;

let candle_action296_batch_scaling_parent_domain =
  candle_action296_batch_scaling_find
    candle_action296_batch_scaling_root_domain
    candle_action296_plan_precision_tree;;

(* The genuine certificate's first pass leaf needs one certified split at    *)
(* coordinate 4.  Its left child is the accepted fixed root of this probe.   *)
let candle_action296_batch_scaling_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_batch_scaling_parent_domain;;

let candle_action296_batch_scaling_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_batch_scaling_probe_lower,
    candle_action296_batch_scaling_probe_upper =
  candle_action296_batch_scaling_domain_bounds
    candle_action296_batch_scaling_probe_domain;;

let _ =
  candle_action296_batch_scaling_marker
    "shared" "whole-box-source-preparation" "begin";;
let candle_action296_batch_scaling_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_batch_scaling_probe_lower
    candle_action296_batch_scaling_probe_upper;;
let _ =
  candle_action296_batch_scaling_marker
    "shared" "whole-box-source-preparation" "end";;

let _ =
  candle_action296_batch_scaling_marker
    "shared" "point-plan-compilation" "begin";;
let candle_action296_batch_scaling_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_action296_batch_scaling_box_prepared;;
let _ =
  candle_action296_batch_scaling_marker
    "shared" "point-plan-compilation" "end";;

let candle_action296_batch_scaling_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_batch_scaling_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_batch_scaling_subdivide remaining
        (List.flatten
          (map (candle_action296_batch_scaling_split axis) domains));;

let candle_action296_batch_scaling_domains_1 =
  [candle_action296_batch_scaling_probe_domain];;
let candle_action296_batch_scaling_domains_8 =
  candle_action296_batch_scaling_subdivide [1;2;3]
    candle_action296_batch_scaling_domains_1;;
let candle_action296_batch_scaling_domains_64 =
  candle_action296_batch_scaling_subdivide [1;2;3;4;5;6]
    candle_action296_batch_scaling_domains_1;;

let candle_action296_batch_scaling_cell domain_th =
  let lower,upper = candle_action296_batch_scaling_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_batch_scaling_box_prepared
      candle_action296_batch_scaling_point_plan lower upper in
  {
    batch_center_variant = center_variant;
    batch_lower = lower;
    batch_upper = upper;
  };;

let candle_action296_batch_scaling_prepare scope domains =
  candle_action296_batch_scaling_marker scope "per-box-preparation" "begin";
  let cells = map candle_action296_batch_scaling_cell domains in
  candle_action296_batch_scaling_marker scope "per-box-preparation" "end";
  cells;;

let candle_action296_batch_scaling_cells_1 =
  candle_action296_batch_scaling_prepare
    "boxes-1" candle_action296_batch_scaling_domains_1;;
let candle_action296_batch_scaling_cells_8 =
  candle_action296_batch_scaling_prepare
    "boxes-8" candle_action296_batch_scaling_domains_8;;
let candle_action296_batch_scaling_cells_64 =
  candle_action296_batch_scaling_prepare
    "boxes-64" candle_action296_batch_scaling_domains_64;;

if length candle_action296_batch_scaling_cells_1 <> 1 ||
   length candle_action296_batch_scaling_cells_8 <> 8 ||
   length candle_action296_batch_scaling_cells_64 <> 64 then
  failwith "action296 batch scaling: subdivision cardinality drift";;

let candle_action296_batch_scaling_scope = ref "unscoped";;
let candle_action296_batch_scaling_profile_events = ref 0;;

let candle_action296_batch_scaling_profile event =
  candle_action296_batch_scaling_profile_events :=
    !candle_action296_batch_scaling_profile_events + 1;
  let scope = !candle_action296_batch_scaling_scope in
  if event = "certified-taylor-batch-compute-begin" then
    candle_action296_batch_scaling_marker scope "kernel-compute" "begin"
  else if event = "certified-taylor-batch-compute-end" then
    candle_action296_batch_scaling_marker scope "kernel-compute" "end"
  else if event = "certified-taylor-batch-call-encoding-begin" then
    candle_action296_batch_scaling_marker scope "call-encoding" "begin"
  else if event = "certified-taylor-batch-call-encoding-end" then
    candle_action296_batch_scaling_marker scope "call-encoding" "end"
  else if event = "certified-taylor-batch-cell-erasure-begin" then
    candle_action296_batch_scaling_marker scope "cell-erasure" "begin"
  else if event = "certified-taylor-batch-cell-erasure-end" then
    candle_action296_batch_scaling_marker scope "cell-erasure" "end"
  else
    print_endline
      ("CANDLE_CV_ACTION296_BATCH_SCALING_STAGE scope=" ^ scope ^
       " event=" ^ event);;

let _ =
  candle_q_dim_analytic_jet_profile :=
    candle_action296_batch_scaling_profile;;

let candle_action296_batch_scaling_empty_control scope =
  candle_action296_batch_scaling_marker scope "empty-kernel-compute" "begin";
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_batch_check`,
       [candle_action296_batch_scaling_box_prepared.
          program_representation_term;
        `Cexp_num 0`]) in
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_taylor_model_batch_compute_eqs call in
  candle_action296_batch_scaling_marker scope "empty-kernel-compute" "end";
  if hyp theorem <> [] || not (aconv (rand (concl theorem)) `Cexp_num 1`) then
    failwith "action296 batch scaling: empty control mismatch";
  theorem;;

let candle_action296_batch_scaling_control_before =
  candle_action296_batch_scaling_empty_control "control-before";;

let candle_action296_batch_scaling_run scope cells =
  candle_action296_batch_scaling_scope := scope;
  candle_action296_batch_scaling_marker scope "batch-total" "begin";
  let result =
    candle_q_dim_taylor_model_batch_prove_six
      candle_action296_batch_scaling_box_prepared cells in
  candle_action296_batch_scaling_marker scope "batch-total" "end";
  if length result.batch_cells <> length cells ||
     hyp result.batch_accept_theorem <> [] then
    failwith "action296 batch scaling: result mismatch";
  result;;

let candle_action296_batch_scaling_result_1 =
  candle_action296_batch_scaling_run
    "boxes-1" candle_action296_batch_scaling_cells_1;;
let candle_action296_batch_scaling_result_8 =
  candle_action296_batch_scaling_run
    "boxes-8" candle_action296_batch_scaling_cells_8;;
let candle_action296_batch_scaling_result_64 =
  candle_action296_batch_scaling_run
    "boxes-64" candle_action296_batch_scaling_cells_64;;

let candle_action296_batch_scaling_control_after =
  candle_action296_batch_scaling_empty_control "control-after";;

let candle_action296_batch_scaling_axioms_after = axioms ();;

if length candle_action296_batch_scaling_axioms_after <>
     length candle_action296_batch_scaling_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_batch_scaling_axioms_before)
       candle_action296_batch_scaling_axioms_after) then
  failwith "action296 batch scaling: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_BATCH_SCALING_RESULT boxes=1,8,64" ^
   " shared_source_preparations=1 internal_computes=5" ^
   " accepted=73 profile_events=" ^
   string_of_int !candle_action296_batch_scaling_profile_events);;
print_endline
  "CANDLE_CV_ACTION296_BATCH_SCALING_OK DEVELOPMENT_NON_RELEASE";;
