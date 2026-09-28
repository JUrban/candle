(* ========================================================================== *)
(* Proof-producing stable-source batches on genuine action-296 cells.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  One authenticated analytic expression and its *)
(* compiled program are reused while exact square-root certificates and boxes *)
(* remain data.  A single reflected verdict proves each 1/8/32-cell family.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_stable_batch_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;

let candle_action296_stable_batch_prove_axioms_before = axioms ();;

let candle_action296_stable_batch_prove_scope = ref "setup";;

let candle_action296_stable_batch_prove_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-stable-batch-proof scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      if event =
           "stable-certified-taylor-batch-preparation-begin" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "proof-input-preparation" "begin"
      else if event =
           "stable-certified-taylor-batch-preparation-end" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "proof-input-preparation" "end"
      else if event =
           "stable-certified-taylor-batch-compute-begin" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "kernel-compute" "begin"
      else if event =
           "stable-certified-taylor-batch-compute-end" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "kernel-compute" "end"
      else if event =
           "stable-certified-taylor-batch-handoff-begin" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "verdict-handoff" "begin"
      else if event =
           "stable-certified-taylor-batch-handoff-end" then
        candle_action296_stable_batch_prove_marker
          !candle_action296_stable_batch_prove_scope
          "verdict-handoff" "end"
      else ());;

let candle_action296_stable_batch_prove_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_stable_batch_prove_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 stable batch proof: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 stable batch proof: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_stable_batch_prove_find left_domain left
  | P_result_mono _ ->
      failwith "action296 stable batch proof: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 stable batch proof: unexpected reference node";;

let candle_action296_stable_batch_prove_parent_domain =
  candle_action296_stable_batch_prove_find
    candle_action296_stable_batch_prove_root_domain
    candle_action296_plan_precision_tree;;

(* The first genuine pass leaf needs one certified split at coordinate four. *)
let candle_action296_stable_batch_prove_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_stable_batch_prove_parent_domain;;

let candle_action296_stable_batch_prove_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_stable_batch_prove_probe_lower,
    candle_action296_stable_batch_prove_probe_upper =
  candle_action296_stable_batch_prove_domain_bounds
    candle_action296_stable_batch_prove_probe_domain;;

let candle_action296_stable_batch_prove_point_plan =
  candle_action296_stable_batch_prove_marker
    "shared" "point-plan-compilation" "begin";
  let result =
    candle_q_dim_taylor_model_point_plan_six
      candle_action296_plan_prepared in
  candle_action296_stable_batch_prove_marker
    "shared" "point-plan-compilation" "end";
  result;;

let candle_action296_stable_batch_prove_variables =
  candle_poly_vector_components
    candle_action296_plan_prepared.vector_term 6;;

let candle_action296_stable_batch_prove_box_intervals lower upper =
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  candle_analytic_collect_sqrt_intervals
    (candle_q_box_sqrt_callback
      candle_action296_stable_batch_prove_variables bounds)
    candle_action296_stable_batch_prove_variables
    candle_action296_plan_prepared.source_term;;

let candle_action296_stable_batch_prove_box_intervals_value =
  candle_action296_stable_batch_prove_marker
    "shared" "whole-box-certificate-data" "begin";
  let result =
    candle_action296_stable_batch_prove_box_intervals
      candle_action296_stable_batch_prove_probe_lower
      candle_action296_stable_batch_prove_probe_upper in
  candle_action296_stable_batch_prove_marker
    "shared" "whole-box-certificate-data" "end";
  result;;

if length candle_action296_stable_batch_prove_box_intervals_value <> 7 then
  failwith "action296 stable batch proof: square-root slot count drift";;

let candle_action296_stable_batch_prove_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_stable_batch_prove_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_stable_batch_prove_subdivide remaining
        (List.flatten
          (map (candle_action296_stable_batch_prove_split axis) domains));;

let candle_action296_stable_batch_prove_domains_1 =
  [candle_action296_stable_batch_prove_probe_domain];;
let candle_action296_stable_batch_prove_domains_8 =
  candle_action296_stable_batch_prove_subdivide [1;2;3]
    candle_action296_stable_batch_prove_domains_1;;
let candle_action296_stable_batch_prove_domains_32 =
  candle_action296_stable_batch_prove_subdivide [1;2;3;4;5]
    candle_action296_stable_batch_prove_domains_1;;

type candle_action296_stable_batch_prove_bounds = {
  stable_batch_prove_lower : term list;
  stable_batch_prove_upper : term list;
};;

let candle_action296_stable_batch_prove_bounds domain_th =
  let lower,upper =
    candle_action296_stable_batch_prove_domain_bounds domain_th in
  {stable_batch_prove_lower = lower;
   stable_batch_prove_upper = upper};;

let candle_action296_stable_batch_prove_cell bounds =
  let lower = bounds.stable_batch_prove_lower and
      upper = bounds.stable_batch_prove_upper in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_action296_stable_batch_prove_point_plan lower upper in
  if length center_intervals <> 7 then
    failwith "action296 stable batch proof: center slot count drift";
  {stable_batch_center_intervals = center_intervals;
   stable_batch_lower = lower;
   stable_batch_upper = upper};;

let candle_action296_stable_batch_prove_prepare_bounds scope domains =
  candle_action296_stable_batch_prove_marker
    scope "domain-normalization" "begin";
  let result = map candle_action296_stable_batch_prove_bounds domains in
  candle_action296_stable_batch_prove_marker
    scope "domain-normalization" "end";
  result;;

let candle_action296_stable_batch_prove_prepare_cells scope bounds =
  candle_action296_stable_batch_prove_marker
    scope "certificate-data" "begin";
  let result = map candle_action296_stable_batch_prove_cell bounds in
  candle_action296_stable_batch_prove_marker
    scope "certificate-data" "end";
  result;;

let candle_action296_stable_batch_prove_bounds_1 =
  candle_action296_stable_batch_prove_prepare_bounds
    "boxes-1" candle_action296_stable_batch_prove_domains_1;;
let candle_action296_stable_batch_prove_bounds_8 =
  candle_action296_stable_batch_prove_prepare_bounds
    "boxes-8" candle_action296_stable_batch_prove_domains_8;;
let candle_action296_stable_batch_prove_bounds_32 =
  candle_action296_stable_batch_prove_prepare_bounds
    "boxes-32" candle_action296_stable_batch_prove_domains_32;;

let candle_action296_stable_batch_prove_cells_1 =
  candle_action296_stable_batch_prove_prepare_cells
    "boxes-1" candle_action296_stable_batch_prove_bounds_1;;
let candle_action296_stable_batch_prove_cells_8 =
  candle_action296_stable_batch_prove_prepare_cells
    "boxes-8" candle_action296_stable_batch_prove_bounds_8;;
let candle_action296_stable_batch_prove_cells_32 =
  candle_action296_stable_batch_prove_prepare_cells
    "boxes-32" candle_action296_stable_batch_prove_bounds_32;;

if length candle_action296_stable_batch_prove_cells_1 <> 1 ||
   length candle_action296_stable_batch_prove_cells_8 <> 8 ||
   length candle_action296_stable_batch_prove_cells_32 <> 32 then
  failwith "action296 stable batch proof: subdivision cardinality drift";;

let candle_action296_stable_batch_prove_run scope cells =
  candle_action296_stable_batch_prove_scope := scope;
  candle_action296_stable_batch_prove_marker
    scope "one-verdict-proof" "begin";
  let result =
    candle_q_dim_taylor_model_stable_batch_prove_six
      candle_action296_plan_prepared
      candle_action296_stable_batch_prove_box_intervals_value cells in
  candle_action296_stable_batch_prove_marker
    scope "one-verdict-proof" "end";
  result;;

let candle_action296_stable_batch_prove_result_1 =
  candle_action296_stable_batch_prove_run
    "boxes-1" candle_action296_stable_batch_prove_cells_1;;
let candle_action296_stable_batch_prove_result_8 =
  candle_action296_stable_batch_prove_run
    "boxes-8" candle_action296_stable_batch_prove_cells_8;;
let candle_action296_stable_batch_prove_result_32 =
  candle_action296_stable_batch_prove_run
    "boxes-32" candle_action296_stable_batch_prove_cells_32;;

let candle_action296_stable_batch_prove_sources scope result cells =
  candle_action296_stable_batch_prove_marker
    scope "source-theorem-extraction" "begin";
  let theorems =
    map
      (candle_q_dim_taylor_model_stable_batch_cell_source_six result)
      cells in
  candle_action296_stable_batch_prove_marker
    scope "source-theorem-extraction" "end";
  theorems;;

let candle_action296_stable_batch_prove_sources_1 =
  candle_action296_stable_batch_prove_sources
    "boxes-1" candle_action296_stable_batch_prove_result_1
    candle_action296_stable_batch_prove_cells_1;;
let candle_action296_stable_batch_prove_sources_8 =
  candle_action296_stable_batch_prove_sources
    "boxes-8" candle_action296_stable_batch_prove_result_8
    candle_action296_stable_batch_prove_cells_8;;
let candle_action296_stable_batch_prove_sources_32 =
  candle_action296_stable_batch_prove_sources
    "boxes-32" candle_action296_stable_batch_prove_result_32
    candle_action296_stable_batch_prove_cells_32;;

let candle_action296_stable_batch_prove_digest theorems =
  Digest.to_hex
    (Digest.string (String.concat "\n" (map string_of_thm theorems)));;

let candle_action296_stable_batch_prove_source_digest_1 =
  candle_action296_stable_batch_prove_digest
    candle_action296_stable_batch_prove_sources_1;;
let candle_action296_stable_batch_prove_source_digest_8 =
  candle_action296_stable_batch_prove_digest
    candle_action296_stable_batch_prove_sources_8;;
let candle_action296_stable_batch_prove_source_digest_32 =
  candle_action296_stable_batch_prove_digest
    candle_action296_stable_batch_prove_sources_32;;

(* Exact payload cardinality is enforced by the reflected checker itself. *)
let candle_action296_stable_batch_prove_expect_rejection label intervals =
  let rejected =
    try
      let _ =
        candle_q_dim_taylor_model_stable_batch_prove_six
          candle_action296_plan_prepared intervals
          candle_action296_stable_batch_prove_cells_1 in
      false
    with Failure _ -> true in
  if not rejected then
    failwith
      ("action296 stable batch proof: negative test accepted " ^ label);;

let _ =
  candle_action296_stable_batch_prove_scope := "adversarial";
  candle_action296_stable_batch_prove_marker
    "adversarial" "payload-cardinality" "begin";
  candle_action296_stable_batch_prove_expect_rejection
    "missing-whole-box-payload"
    (tl candle_action296_stable_batch_prove_box_intervals_value);
  candle_action296_stable_batch_prove_expect_rejection
    "extra-whole-box-payload"
    (hd candle_action296_stable_batch_prove_box_intervals_value ::
     candle_action296_stable_batch_prove_box_intervals_value);
  candle_action296_stable_batch_prove_marker
    "adversarial" "payload-cardinality" "end";;

let candle_action296_stable_batch_prove_all_sources =
  candle_action296_stable_batch_prove_sources_1 @
  candle_action296_stable_batch_prove_sources_8 @
  candle_action296_stable_batch_prove_sources_32;;

let candle_action296_stable_batch_prove_axioms_after = axioms ();;

if length candle_action296_stable_batch_prove_all_sources <> 41 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       candle_action296_stable_batch_prove_all_sources) ||
   hyp candle_action296_stable_batch_prove_result_1.
         stable_batch_accept_theorem <> [] ||
   hyp candle_action296_stable_batch_prove_result_8.
         stable_batch_accept_theorem <> [] ||
   hyp candle_action296_stable_batch_prove_result_32.
         stable_batch_accept_theorem <> [] ||
   length candle_action296_stable_batch_prove_axioms_after <>
     length candle_action296_stable_batch_prove_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_stable_batch_prove_axioms_before)
       candle_action296_stable_batch_prove_axioms_after) then
  failwith "action296 stable batch proof: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_STABLE_BATCH_PROVE_RESULT boxes=1,8,32" ^
   " accepted=41 computes=3 source_theorems=41" ^
   " stable_programs=1 sqrt_slots=7 adversarial_rejections=2" ^
   " source_digest_1=" ^
     candle_action296_stable_batch_prove_source_digest_1 ^
   " source_digest_8=" ^
     candle_action296_stable_batch_prove_source_digest_8 ^
   " source_digest_32=" ^
     candle_action296_stable_batch_prove_source_digest_32);;
print_endline
  "CANDLE_CV_ACTION296_STABLE_BATCH_PROVE_OK DEVELOPMENT_NON_RELEASE";;
