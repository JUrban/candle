(* ========================================================================== *)
(* Fixed-scale discriminator for the two dominant action-296 polynomial      *)
(* blocks.                                                                    *)
(*                                                                            *)
(* DEVELOPMENT / DIAGNOSTIC ONLY.  The ordinary evaluator is untrusted and   *)
(* never authorizes a theorem.  All sixteen complete block results (two       *)
(* blocks over eight distinct boxes) must equal Kernel.compute exactly.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_diagnostic.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_fixed_scale_diagnostic;;
open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_action296_fixed_scale_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-scale scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fixed_scale_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_action296_fixed_scale_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 fixed scale: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 fixed scale: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fixed_scale_find left_domain left
  | P_result_mono _ ->
      failwith "action296 fixed scale: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 fixed scale: unexpected reference node";;

let candle_action296_fixed_scale_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_fixed_scale_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_fixed_scale_subdivide remaining
        (List.flatten
          (map (candle_action296_fixed_scale_split axis) domains));;

let candle_action296_fixed_scale_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_certified_compute_eqs tm;;

let candle_action296_reflected_fixed_scale_compute tm =
  candle_q_dim_analytic_jet_compute candle_cv_fs_compute_eqs tm;;

let candle_action296_fixed_scale_poly_payload instruction =
  let tag,payload = candle_cv_fixed_term_pair instruction in
  if candle_cv_fixed_term_int tag <> 0 then
    failwith "action296 fixed scale: expected polynomial instruction";
  payload;;

let rec candle_action296_fixed_scale_nth index = function
  | [] -> failwith "action296 fixed scale: instruction index outside program"
  | head :: tail ->
      if index = 0 then head
      else candle_action296_fixed_scale_nth (index - 1) tail;;

type candle_action296_fixed_scale_case = {
  candle_action296_fixed_scale_boxes_term: term;
  candle_action296_fixed_scale_center_boxes_term: term;
  candle_action296_fixed_scale_radii_term: term;
  candle_action296_fixed_scale_center_boxes:
    candle_cv_fixed_interval array;
  candle_action296_fixed_scale_radii: Num.num array
};;

let candle_action296_fixed_scale_run () =
  let axioms_before = axioms () in
  candle_action296_fixed_scale_marker "batch" "profiled-run" "begin";
  let root_domain =
    M_taylor.mk_m_center_domain
      candle_action296_plan_dimension 6
      candle_action296_plan_xx1 candle_action296_plan_zz1 in
  let parent_domain =
    candle_action296_fixed_scale_find
      root_domain candle_action296_plan_precision_tree in
  let probe_domain,_ =
    M_verifier.split_domain candle_action296_plan_dimension 6 4
      parent_domain in
  let probe_lower,probe_upper =
    candle_action296_fixed_scale_domain_bounds probe_domain in
  candle_action296_fixed_scale_marker
    "shared" "whole-box-source-preparation" "begin";
  let box_prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term probe_lower probe_upper in
  candle_action296_fixed_scale_marker
    "shared" "whole-box-source-preparation" "end";
  let domains =
    candle_action296_fixed_scale_subdivide [1;2;3] [probe_domain] in
  let bounds = map candle_action296_fixed_scale_domain_bounds domains in
  if length bounds <> 8 then
    failwith "action296 fixed scale: case cardinality drift";
  let top_program =
    candle_cv_fixed_term_list box_prepared.program_representation_term in
  if length top_program <> 54 then
    failwith "action296 fixed scale: top program cardinality drift";
  let instruction32 = candle_action296_fixed_scale_nth 32 top_program in
  let instruction33 = candle_action296_fixed_scale_nth 33 top_program in
  let block32 = candle_action296_fixed_scale_poly_payload instruction32 in
  let block33 = candle_action296_fixed_scale_poly_payload instruction33 in
  candle_action296_fixed_scale_marker
    "shared" "fixed-program-compilation" "begin";
  let compiled32 = candle_cv_fixed_polynomial_compile block32 and
      compiled33 = candle_cv_fixed_polynomial_compile block33 in
  candle_action296_fixed_scale_marker
    "shared" "fixed-program-compilation" "end";
  if Array.length compiled32 <> 39 || Array.length compiled33 <> 85 then
    failwith "action296 fixed scale: polynomial cardinality drift";
  candle_action296_fixed_scale_marker "boxes-8" "box-setup" "begin";
  let cases =
    map
      (fun (lower,upper) ->
        let boxes = candle_poly_fixture_q_boxes lower upper in
        let boxes_representation =
          candle_q_dim_analytic_jet_boxes_encode_conv boxes in
        let boxes_term = rand (concl boxes_representation) in
        let center_boxes_th =
          candle_action296_fixed_scale_compute
            (mk_comb (`candle_cv_q_center_environment_list`,boxes_term)) in
        let center_boxes_term = rand (concl center_boxes_th) in
        let radii_th =
          candle_action296_fixed_scale_compute
            (mk_comb
              (`candle_cv_q_fixed_list_round_upper`,
               mk_comb (`candle_cv_q_radius_list`,boxes_term))) in
        let radii_term = rand (concl radii_th) in
        {candle_action296_fixed_scale_boxes_term = boxes_term;
         candle_action296_fixed_scale_center_boxes_term = center_boxes_term;
         candle_action296_fixed_scale_radii_term = radii_term;
         candle_action296_fixed_scale_center_boxes =
           candle_cv_fixed_term_center_boxes center_boxes_term;
         candle_action296_fixed_scale_radii =
           candle_cv_fixed_term_scaled_rational_list radii_term})
      bounds in
  candle_action296_fixed_scale_marker "boxes-8" "box-setup" "end";
  let execute_blocks case =
    candle_cv_fixed_polynomial_execute
      case.candle_action296_fixed_scale_radii
      case.candle_action296_fixed_scale_center_boxes compiled32,
    candle_cv_fixed_polynomial_execute
      case.candle_action296_fixed_scale_radii
      case.candle_action296_fixed_scale_center_boxes compiled33 in
  candle_action296_fixed_scale_marker
    "boxes-8" "fixed-scale-first" "begin";
  let fixed_results = map execute_blocks cases in
  candle_action296_fixed_scale_marker
    "boxes-8" "fixed-scale-first" "end";
  candle_action296_fixed_scale_marker
    "boxes-8" "fixed-output-conversion" "begin";
  let fixed_terms =
    map
      (fun (left,right) ->
        candle_cv_fixed_result_term left,candle_cv_fixed_result_term right)
      fixed_results in
  candle_action296_fixed_scale_marker
    "boxes-8" "fixed-output-conversion" "end";
  candle_action296_fixed_scale_marker "boxes-8" "kernel-blocks" "begin";
  let kernel_theorems =
    map
      (fun case ->
        candle_action296_fixed_scale_compute
          (list_mk_comb
            (`candle_cv_q_dim_taylor_model_poly_program`,
             [case.candle_action296_fixed_scale_center_boxes_term;
              case.candle_action296_fixed_scale_boxes_term;
              case.candle_action296_fixed_scale_radii_term;block32])),
        candle_action296_fixed_scale_compute
          (list_mk_comb
            (`candle_cv_q_dim_taylor_model_poly_program`,
             [case.candle_action296_fixed_scale_center_boxes_term;
              case.candle_action296_fixed_scale_boxes_term;
              case.candle_action296_fixed_scale_radii_term;block33])))
      cases in
  candle_action296_fixed_scale_marker "boxes-8" "kernel-blocks" "end";
  candle_action296_fixed_scale_marker
    "boxes-8" "reflected-fixed-blocks" "begin";
  let reflected_fixed_theorems =
    map
      (fun case ->
        candle_action296_reflected_fixed_scale_compute
          (list_mk_comb
            (`candle_cv_fs_poly_program_to_q`,
             [case.candle_action296_fixed_scale_center_boxes_term;
              case.candle_action296_fixed_scale_radii_term;block32])),
        candle_action296_reflected_fixed_scale_compute
          (list_mk_comb
            (`candle_cv_fs_poly_program_to_q`,
             [case.candle_action296_fixed_scale_center_boxes_term;
              case.candle_action296_fixed_scale_radii_term;block33])))
      cases in
  candle_action296_fixed_scale_marker
    "boxes-8" "reflected-fixed-blocks" "end";
  let rec validate_exact count fixed_remaining kernel_remaining =
    match fixed_remaining,kernel_remaining with
    | [],[] -> count
    | (fixed32,fixed33) :: fixed_tail,
      (kernel32,kernel33) :: kernel_tail ->
        if hyp kernel32 <> [] || hyp kernel33 <> [] ||
           not (aconv fixed32 (rand (concl kernel32))) ||
           not (aconv fixed33 (rand (concl kernel33))) then
          failwith "action296 fixed scale: complete block output mismatch";
        validate_exact (count + 2) fixed_tail kernel_tail
    | _ -> failwith "action296 fixed scale: comparison cardinality drift" in
  let exact = validate_exact 0 fixed_terms kernel_theorems in
  let reflected_exact =
    validate_exact 0
      (map
        (fun (left,right) -> rand (concl left),rand (concl right))
        reflected_fixed_theorems)
      kernel_theorems in
  let repetitions = 100 in
  candle_action296_fixed_scale_marker
    "boxes-8x100" "fixed-scale-repeat" "begin";
  let checksum = ref candle_cv_fixed_zero in
  let rec accumulate = function
    | [] -> ()
    | case :: remaining ->
        let left,right = execute_blocks case in
        let _,left_upper = left.candle_cv_fixed_result_value_bound and
            _,right_upper = right.candle_cv_fixed_result_value_bound in
        checksum := Num.add_num !checksum
          (Num.add_num left_upper right_upper);
        accumulate remaining in
  for repetition_index = 1 to repetitions do
    let _ = repetition_index in
    accumulate cases
  done;
  candle_action296_fixed_scale_marker
    "boxes-8x100" "fixed-scale-repeat" "end";
  let axioms_after = axioms () in
  if exact <> 16 || reflected_exact <> 16 ||
     not
       (List.for_all
         (fun (left,right) -> hyp left = [] && hyp right = [])
         reflected_fixed_theorems) ||
     Num.eq_num !checksum candle_cv_fixed_zero ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before) axioms_after) then
    failwith "action296 fixed scale: final validation failed";
  candle_action296_fixed_scale_marker "batch" "profiled-run" "end";
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_SCALE_RESULT boxes=8 blocks=2" ^
     " instructions=39,85 host_exact_outputs=" ^ string_of_int exact ^
     " reflected_exact_outputs=" ^ string_of_int reflected_exact ^
     " repeat_batches=" ^ string_of_int repetitions);
  print_endline
    "CANDLE_CV_ACTION296_FIXED_SCALE_OK DEVELOPMENT_NON_RELEASE";;

let _ = candle_action296_fixed_scale_run ();;
