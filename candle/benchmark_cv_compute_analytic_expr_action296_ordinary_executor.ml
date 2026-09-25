(* ========================================================================== *)
(* Ordinary versus reflected execution of the genuine action-296 program.   *)
(*                                                                            *)
(* DEVELOPMENT / DIAGNOSTIC ONLY.  The ordinary executor is untrusted and    *)
(* never authorizes a theorem.  Eight complete concrete results must match   *)
(* Kernel.compute exactly, and only the kernel theorems validate acceptance. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;
needs "candle/cv_compute_diagnostic_executor.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;

let candle_action296_ordinary_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-ordinary-executor scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_ordinary_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_action296_ordinary_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 ordinary executor: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 ordinary executor: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_ordinary_find left_domain left
  | P_result_mono _ ->
      failwith "action296 ordinary executor: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 ordinary executor: unexpected reference node";;

let candle_action296_ordinary_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_ordinary_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_ordinary_subdivide remaining
        (List.flatten (map (candle_action296_ordinary_split axis) domains));;

let candle_action296_ordinary_stats_add left right =
  {candle_cv_diagnostic_function_calls =
     left.candle_cv_diagnostic_function_calls +
     right.candle_cv_diagnostic_function_calls;
   candle_cv_diagnostic_pair_ops =
     left.candle_cv_diagnostic_pair_ops + right.candle_cv_diagnostic_pair_ops;
   candle_cv_diagnostic_add_ops =
     left.candle_cv_diagnostic_add_ops + right.candle_cv_diagnostic_add_ops;
   candle_cv_diagnostic_sub_ops =
     left.candle_cv_diagnostic_sub_ops + right.candle_cv_diagnostic_sub_ops;
   candle_cv_diagnostic_mul_ops =
     left.candle_cv_diagnostic_mul_ops + right.candle_cv_diagnostic_mul_ops;
   candle_cv_diagnostic_div_ops =
     left.candle_cv_diagnostic_div_ops + right.candle_cv_diagnostic_div_ops;
   candle_cv_diagnostic_mod_ops =
     left.candle_cv_diagnostic_mod_ops + right.candle_cv_diagnostic_mod_ops;
   candle_cv_diagnostic_less_ops =
     left.candle_cv_diagnostic_less_ops + right.candle_cv_diagnostic_less_ops;
   candle_cv_diagnostic_equal_ops =
     left.candle_cv_diagnostic_equal_ops + right.candle_cv_diagnostic_equal_ops;
   candle_cv_diagnostic_projection_ops =
     left.candle_cv_diagnostic_projection_ops +
     right.candle_cv_diagnostic_projection_ops;
   candle_cv_diagnostic_if_ops =
     left.candle_cv_diagnostic_if_ops + right.candle_cv_diagnostic_if_ops;
   candle_cv_diagnostic_let_ops =
     left.candle_cv_diagnostic_let_ops + right.candle_cv_diagnostic_let_ops;
   candle_cv_diagnostic_max_depth =
     max left.candle_cv_diagnostic_max_depth
       right.candle_cv_diagnostic_max_depth};;

let candle_action296_ordinary_zero_stats =
  {candle_cv_diagnostic_function_calls = 0;
   candle_cv_diagnostic_pair_ops = 0;
   candle_cv_diagnostic_add_ops = 0;
   candle_cv_diagnostic_sub_ops = 0;
   candle_cv_diagnostic_mul_ops = 0;
   candle_cv_diagnostic_div_ops = 0;
   candle_cv_diagnostic_mod_ops = 0;
   candle_cv_diagnostic_less_ops = 0;
   candle_cv_diagnostic_equal_ops = 0;
   candle_cv_diagnostic_projection_ops = 0;
   candle_cv_diagnostic_if_ops = 0;
   candle_cv_diagnostic_let_ops = 0;
   candle_cv_diagnostic_max_depth = 0};;

let candle_action296_ordinary_run () =
  let axioms_before = axioms () in
  candle_action296_ordinary_marker "batch" "profiled-run" "begin";
  let root_domain =
    M_taylor.mk_m_center_domain
      candle_action296_plan_dimension 6
      candle_action296_plan_xx1 candle_action296_plan_zz1 in
  let parent_domain =
    candle_action296_ordinary_find
      root_domain candle_action296_plan_precision_tree in
  let probe_domain,_ =
    M_verifier.split_domain candle_action296_plan_dimension 6 4
      parent_domain in
  let probe_lower,probe_upper =
    candle_action296_ordinary_domain_bounds probe_domain in
  candle_action296_ordinary_marker
    "shared" "whole-box-source-preparation" "begin";
  let box_prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term probe_lower probe_upper in
  candle_action296_ordinary_marker
    "shared" "whole-box-source-preparation" "end";
  let domains = candle_action296_ordinary_subdivide [1;2;3] [probe_domain] in
  candle_action296_ordinary_marker
    "shared" "center-variant-preparation" "begin";
  let cases =
    map
      (fun domain_th ->
        let lower,upper = candle_action296_ordinary_domain_bounds domain_th in
        let variant =
          candle_q_dim_taylor_model_prepare_point_variant_six
            box_prepared lower upper in
        let boxes = candle_poly_fixture_q_boxes lower upper in
        let boxes_representation =
          candle_q_dim_analytic_jet_boxes_encode_conv boxes in
        let boxes_term = rand (concl boxes_representation) in
        let call =
          list_mk_comb
            (`candle_cv_q_dim_taylor_model_program`,
             [variant.variant_program_representation_term;
              box_prepared.program_representation_term;boxes_term]) in
        boxes_term,call)
      domains in
  candle_action296_ordinary_marker
    "shared" "center-variant-preparation" "end";
  if length cases <> 8 then
    failwith "action296 ordinary executor: case cardinality drift";
  candle_action296_ordinary_marker "shared" "equation-compilation" "begin";
  let program =
    candle_cv_diagnostic_compile
      candle_cv_q_dim_taylor_model_certified_compute_eqs in
  candle_action296_ordinary_marker "shared" "equation-compilation" "end";
  candle_action296_ordinary_marker "boxes-8" "input-compilation" "begin";
  let inputs =
    map
      (fun (_,call) -> candle_cv_diagnostic_compile_term program call)
      cases in
  candle_action296_ordinary_marker "boxes-8" "input-compilation" "end";
  candle_action296_ordinary_marker "boxes-8" "ordinary-execution" "begin";
  let ordinary_results =
    map (candle_cv_diagnostic_execute program) inputs in
  candle_action296_ordinary_marker "boxes-8" "ordinary-execution" "end";
  let total_stats =
    List.fold_left
      (fun total (_,stats) -> candle_action296_ordinary_stats_add total stats)
      candle_action296_ordinary_zero_stats ordinary_results in
  candle_cv_diagnostic_stats_line "action296-boxes-8" total_stats;
  candle_action296_ordinary_marker "boxes-8" "output-conversion" "begin";
  let ordinary_terms =
    map (fun (value,_) -> candle_cv_diagnostic_value_term value)
      ordinary_results in
  candle_action296_ordinary_marker "boxes-8" "output-conversion" "end";
  candle_action296_ordinary_marker "boxes-8" "kernel-compute" "begin";
  let kernel_results =
    map
      (fun (_,call) ->
        candle_q_dim_analytic_jet_compute
          candle_cv_q_dim_taylor_model_certified_compute_eqs call)
      cases in
  candle_action296_ordinary_marker "boxes-8" "kernel-compute" "end";
  let rec validate accepted ordinary remaining_cases kernel =
    match ordinary,remaining_cases,kernel with
    | [],[],[] -> accepted
    | ordinary_term :: ordinary_tail,
      (boxes_term,_) :: case_tail,kernel_th :: kernel_tail ->
        if hyp kernel_th <> [] ||
           not (aconv ordinary_term (rand (concl kernel_th))) then
          failwith "action296 ordinary executor: complete output mismatch";
        let finish_th =
          candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_taylor_model_certified_compute_eqs
            (list_mk_comb
              (`candle_cv_q_dim_taylor_model_certified_finish`,
               [boxes_term;rand (concl kernel_th)])) in
        let flag,_ =
          candle_q_dim_analytic_jet_dest_pair (rand (concl finish_th)) in
        if hyp finish_th <> [] || not (aconv flag `Cexp_num 1`) then
          failwith "action296 ordinary executor: accepted box rejected";
        validate (accepted + 1) ordinary_tail case_tail kernel_tail
    | _ -> failwith "action296 ordinary executor: result cardinality mismatch" in
  candle_action296_ordinary_marker "boxes-8" "exact-validation" "begin";
  let accepted = validate 0 ordinary_terms cases kernel_results in
  candle_action296_ordinary_marker "boxes-8" "exact-validation" "end";
  let axioms_after = axioms () in
  if accepted <> 8 || length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before) axioms_after) then
    failwith "action296 ordinary executor: final validation failed";
  candle_action296_ordinary_marker "batch" "profiled-run" "end";
  print_endline
    ("CANDLE_CV_ACTION296_ORDINARY_EXECUTOR_RESULT boxes=8" ^
     " complete_outputs_exact=8 accepted=8 untrusted_ordinary_only=1");
  print_endline
    "CANDLE_CV_ACTION296_ORDINARY_EXECUTOR_OK DEVELOPMENT_NON_RELEASE";;

let _ = candle_action296_ordinary_run ();;
