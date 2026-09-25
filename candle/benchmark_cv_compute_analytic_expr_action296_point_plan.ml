(* ========================================================================== *)
(* Reused square-root argument plan for genuine action-296 preparation.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The untrusted proposer compiles the seven     *)
(* rational square-root arguments once, evaluates them at eight distinct    *)
(* centers, and must reproduce the existing exact proposals.  Kernel.compute*)
(* remains the only authority and validates every resulting complete box.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;

let candle_action296_point_plan_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-point-plan scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_point_plan_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_action296_point_plan_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 point plan: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 point plan: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_point_plan_find left_domain left
  | P_result_mono _ ->
      failwith "action296 point plan: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 point plan: unexpected reference node";;

let candle_action296_point_plan_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_point_plan_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_point_plan_subdivide remaining
        (List.flatten (map (candle_action296_point_plan_split axis) domains));;

let rec candle_action296_point_plan_term_lists_equal left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_point_plan_term_lists_equal left_tail right_tail
  | _ -> false;;

let rec candle_action296_point_plan_nested_equal left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      candle_action296_point_plan_term_lists_equal left_head right_head &&
      candle_action296_point_plan_nested_equal left_tail right_tail
  | _ -> false;;

let candle_action296_point_plan_run () =
  let axioms_before = axioms () in
  candle_action296_point_plan_marker "batch" "profiled-run" "begin";
  let root_domain =
    M_taylor.mk_m_center_domain
      candle_action296_plan_dimension 6
      candle_action296_plan_xx1 candle_action296_plan_zz1 in
  let parent_domain =
    candle_action296_point_plan_find
      root_domain candle_action296_plan_precision_tree in
  let probe_domain,_ =
    M_verifier.split_domain candle_action296_plan_dimension 6 4
      parent_domain in
  let probe_lower,probe_upper =
    candle_action296_point_plan_domain_bounds probe_domain in
  candle_action296_point_plan_marker
    "shared" "whole-box-source-preparation" "begin";
  let box_prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term probe_lower probe_upper in
  candle_action296_point_plan_marker
    "shared" "whole-box-source-preparation" "end";
  let domains = candle_action296_point_plan_subdivide [1;2;3] [probe_domain] in
  let bounds = map candle_action296_point_plan_domain_bounds domains in
  let variables = candle_poly_vector_components box_prepared.vector_term 6 in
  if length bounds <> 8 then
    failwith "action296 point plan: case cardinality drift";
  candle_action296_point_plan_marker "shared" "point-plan-compilation" "begin";
  let plan = candle_q_dim_taylor_model_point_plan_six box_prepared in
  candle_action296_point_plan_marker "shared" "point-plan-compilation" "end";
  if length plan.point_plan_programs <> 7 then
    failwith "action296 point plan: square-root cardinality drift";
  let ordinary_intervals () =
    map
      (fun (lower,upper) ->
        let values = candle_q_point_centers lower upper in
        candle_analytic_collect_sqrt_intervals
          (candle_q_point_sqrt_callback variables values)
          variables box_prepared.source_term)
      bounds in
  let planned_intervals () =
    map
      (fun (lower,upper) ->
        candle_q_dim_taylor_model_point_plan_intervals_six
          plan lower upper)
      bounds in
  candle_action296_point_plan_marker "boxes-8" "ordinary-hints-first" "begin";
  let ordinary_first = ordinary_intervals () in
  candle_action296_point_plan_marker "boxes-8" "ordinary-hints-first" "end";
  candle_action296_point_plan_marker "boxes-8" "planned-hints-first" "begin";
  let planned_first = planned_intervals () in
  candle_action296_point_plan_marker "boxes-8" "planned-hints-first" "end";
  candle_action296_point_plan_marker "boxes-8" "planned-hints-repeat" "begin";
  let planned_repeat = planned_intervals () in
  candle_action296_point_plan_marker "boxes-8" "planned-hints-repeat" "end";
  candle_action296_point_plan_marker "boxes-8" "ordinary-hints-repeat" "begin";
  let ordinary_repeat = ordinary_intervals () in
  candle_action296_point_plan_marker "boxes-8" "ordinary-hints-repeat" "end";
  if not (candle_action296_point_plan_nested_equal ordinary_first planned_first) ||
     not (candle_action296_point_plan_nested_equal ordinary_first planned_repeat) ||
     not (candle_action296_point_plan_nested_equal ordinary_first ordinary_repeat)
  then failwith "action296 point plan: exact proposal mismatch";
  candle_action296_point_plan_marker
    "boxes-8" "planned-variant-preparation" "begin";
  let variants =
    map
      (fun (lower,upper) ->
        lower,upper,
        candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
          box_prepared plan lower upper)
      bounds in
  candle_action296_point_plan_marker
    "boxes-8" "planned-variant-preparation" "end";
  let first_lower,first_upper,first_variant = hd variants in
  candle_action296_point_plan_marker
    "box-1" "ordinary-variant-oracle" "begin";
  let first_oracle =
    candle_q_dim_taylor_model_prepare_point_variant_six
      box_prepared first_lower first_upper in
  candle_action296_point_plan_marker
    "box-1" "ordinary-variant-oracle" "end";
  if not
      (aconv first_variant.variant_expression_term
        first_oracle.variant_expression_term) ||
     not
      (aconv first_variant.variant_program_representation_term
        first_oracle.variant_program_representation_term) then
    failwith "action296 point plan: prepared variant mismatch";
  candle_action296_point_plan_marker "boxes-8" "kernel-validation" "begin";
  let accepted =
    List.fold_left
      (fun count (lower,upper,variant) ->
        let boxes = candle_poly_fixture_q_boxes lower upper in
        let boxes_representation =
          candle_q_dim_analytic_jet_boxes_encode_conv boxes in
        let boxes_term = rand (concl boxes_representation) in
        let program_th =
          candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_taylor_model_certified_compute_eqs
            (list_mk_comb
              (`candle_cv_q_dim_taylor_model_program`,
               [variant.variant_program_representation_term;
                box_prepared.program_representation_term;boxes_term])) in
        let finish_th =
          candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_taylor_model_certified_compute_eqs
            (list_mk_comb
              (`candle_cv_q_dim_taylor_model_certified_finish`,
               [boxes_term;rand (concl program_th)])) in
        let flag,_ =
          candle_q_dim_analytic_jet_dest_pair (rand (concl finish_th)) in
        if hyp program_th <> [] || hyp finish_th <> [] ||
           not (aconv flag `Cexp_num 1`) then
          failwith "action296 point plan: reflected validation failed";
        count + 1)
      0 variants in
  candle_action296_point_plan_marker "boxes-8" "kernel-validation" "end";
  let axioms_after = axioms () in
  if accepted <> 8 || length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before) axioms_after) then
    failwith "action296 point plan: final validation failed";
  candle_action296_point_plan_marker "batch" "profiled-run" "end";
  print_endline
    ("CANDLE_CV_ACTION296_POINT_PLAN_RESULT boxes=8 sqrt_programs=7" ^
     " exact_intervals=56 exact_variant=1 accepted=8");
  print_endline
    "CANDLE_CV_ACTION296_POINT_PLAN_OK DEVELOPMENT_NON_RELEASE";;

let _ = candle_action296_point_plan_run ();;
