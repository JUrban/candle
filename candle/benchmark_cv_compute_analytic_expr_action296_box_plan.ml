(* ========================================================================== *)
(* Exact compiled whole-box hint preparation on genuine action-296 boxes.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Compare the existing HOL-term traversal with  *)
(* execution of the source-only rational programs already compiled for point *)
(* hints.  Both paths remain untrusted preparation; the reflected checker is  *)
(* the authority.  Exact candidate equality is required on eight distinct    *)
(* genuine subboxes before reporting the timing discriminator.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;

let candle_action296_box_plan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-box-plan scope=boxes-8 phase=" ^
     phase ^ " event=" ^ event);;

let candle_action296_box_plan_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_box_plan_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 box plan: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 box plan: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_box_plan_find left_domain left
  | P_result_mono _ ->
      failwith "action296 box plan: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 box plan: unexpected reference node";;

let candle_action296_box_plan_parent_domain =
  candle_action296_box_plan_find
    candle_action296_box_plan_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_box_plan_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_box_plan_parent_domain;;

let candle_action296_box_plan_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_box_plan_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_box_plan_subdivide remaining
        (List.flatten
          (map (candle_action296_box_plan_split axis) domains));;

let candle_action296_box_plan_domains =
  candle_action296_box_plan_subdivide [1;2;3]
    [candle_action296_box_plan_probe_domain];;

let candle_action296_box_plan_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_box_plan_bounds =
  map candle_action296_box_plan_domain_bounds
    candle_action296_box_plan_domains;;

let candle_action296_box_plan_variables =
  candle_poly_vector_components
    candle_action296_plan_prepared.vector_term 6;;

let candle_action296_box_plan_legacy lower upper =
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  candle_analytic_collect_sqrt_intervals
    (candle_q_box_sqrt_callback
      candle_action296_box_plan_variables bounds)
    candle_action296_box_plan_variables
    candle_action296_plan_prepared.source_term;;

let candle_action296_box_plan_source_plan =
  candle_action296_box_plan_marker "source-plan-compilation" "begin";
  let result =
    candle_q_dim_taylor_model_point_plan_six
      candle_action296_plan_prepared in
  candle_action296_box_plan_marker "source-plan-compilation" "end";
  result;;

let _ = candle_action296_box_plan_marker "legacy-preparation" "begin";;
let candle_action296_box_plan_legacy_results =
  map
    (fun (lower,upper) -> candle_action296_box_plan_legacy lower upper)
    candle_action296_box_plan_bounds;;
let _ = candle_action296_box_plan_marker "legacy-preparation" "end";;

let _ = candle_action296_box_plan_marker "compiled-preparation" "begin";;
let candle_action296_box_plan_compiled_results =
  map
    (fun (lower,upper) ->
      candle_q_box_rational_program_intervals_six
        candle_action296_box_plan_source_plan.point_plan_programs
        lower upper)
    candle_action296_box_plan_bounds;;
let _ = candle_action296_box_plan_marker "compiled-preparation" "end";;

let rec candle_action296_box_plan_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_box_plan_aconv_lists left_tail right_tail
  | _ -> false;;

let rec candle_action296_box_plan_aconv_batches left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      candle_action296_box_plan_aconv_lists left_head right_head &&
      candle_action296_box_plan_aconv_batches left_tail right_tail
  | _ -> false;;

let candle_action296_box_plan_exact =
  length candle_action296_box_plan_legacy_results = 8 &&
  length candle_action296_box_plan_compiled_results = 8 &&
  List.for_all
    (fun intervals -> length intervals = 7)
    candle_action296_box_plan_compiled_results &&
  candle_action296_box_plan_aconv_batches
    candle_action296_box_plan_legacy_results
    candle_action296_box_plan_compiled_results;;

let candle_action296_box_plan_expect_rejection label program =
  let rejected =
    try
      let _ = candle_q_box_rational_program_interval [] program in
      false
    with Failure _ -> true in
  if not rejected then
    failwith ("action296 box plan: accepted " ^ label);;

let candle_action296_box_plan_one =
  Candle_q_point_rational_constant (Num.num_of_int 1);;

let _ =
  candle_action296_box_plan_expect_rejection "division"
    (Candle_q_point_rational_div
      (candle_action296_box_plan_one,candle_action296_box_plan_one));
  candle_action296_box_plan_expect_rejection "inverse"
    (Candle_q_point_rational_inv candle_action296_box_plan_one);
  candle_action296_box_plan_expect_rejection "non-square-power"
    (Candle_q_point_rational_pow
      (candle_action296_box_plan_one,Num.num_of_int 3));;

let _ = candle_action296_box_plan_marker "comparison" "begin";;
if not candle_action296_box_plan_exact then
  failwith "action296 box plan: compiled candidates differ from legacy";;
let _ = candle_action296_box_plan_marker "comparison" "end";;

print_endline
  ("CANDLE_CV_ACTION296_BOX_PLAN_RESULT boxes=8 sqrt_slots=7 exact=true" ^
   " adversarial_rejections=3");;
print_endline
  "CANDLE_CV_ACTION296_BOX_PLAN_OK DEVELOPMENT_NON_RELEASE";;
