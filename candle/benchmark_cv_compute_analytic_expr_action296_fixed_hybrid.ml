(* ========================================================================== *)
(* Whole-checker discriminator for fixed-scale action-296 polynomial blocks. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Two genuine sibling cells are prepared once. *)
(* The established rational Taylor interpreter and a diagnostic hybrid that *)
(* sends tag-0 polynomial instructions through the fixed-scale backend then  *)
(* execute the same complete certified check.  One compact verdict crosses  *)
(* the evaluator boundary for each two-cell batch; complete outputs are also *)
(* compared cell by cell.  The hybrid has no theorem authority until its     *)
(* program invariant has been proved.                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

let candle_action296_fixed_hybrid_axioms_before = axioms ();;

let candle_action296_fixed_hybrid_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-hybrid scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_cv_action296_current_check_batch_def = define
 `(candle_cv_action296_current_check_batch
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_current_check_batch
      box_program (Cexp_pair h t) =
     Cexp_add
       (Cexp_fst
         (candle_cv_q_dim_taylor_model_certified_check
           (Cexp_fst h) box_program (Cexp_snd h)))
       (candle_cv_action296_current_check_batch box_program t))`;;

let candle_cv_action296_current_check_batch_compute = prove
 (`!box_program cases.
     candle_cv_action296_current_check_batch box_program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_add
         (Cexp_fst
           (candle_cv_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst cases)) box_program
             (Cexp_snd (Cexp_fst cases))))
         (candle_cv_action296_current_check_batch
           box_program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_current_check_batch_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_action296_fixed_hybrid_check_batch_def = define
 `(candle_cv_action296_fixed_hybrid_check_batch
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_fixed_hybrid_check_batch
      box_program (Cexp_pair h t) =
     Cexp_add
       (Cexp_fst
         (candle_cv_fs_q_dim_taylor_model_certified_check
           (Cexp_fst h) box_program (Cexp_snd h)))
       (candle_cv_action296_fixed_hybrid_check_batch box_program t))`;;

let candle_cv_action296_fixed_hybrid_check_batch_compute = prove
 (`!box_program cases.
     candle_cv_action296_fixed_hybrid_check_batch box_program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_add
         (Cexp_fst
           (candle_cv_fs_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst cases)) box_program
             (Cexp_snd (Cexp_fst cases))))
         (candle_cv_action296_fixed_hybrid_check_batch
           box_program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_fixed_hybrid_check_batch_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_action296_fixed_hybrid_current_eqs =
  union candle_cv_q_dim_taylor_model_certified_compute_eqs
    [SPEC_ALL candle_cv_action296_current_check_batch_compute];;

let candle_action296_fixed_hybrid_hybrid_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    [SPEC_ALL candle_cv_action296_fixed_hybrid_check_batch_compute];;

let candle_action296_fixed_hybrid_compute equations tm =
  candle_q_dim_analytic_jet_compute equations tm;;

let candle_action296_fixed_hybrid_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_fixed_hybrid_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 fixed hybrid: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 fixed hybrid: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fixed_hybrid_find left_domain left
  | P_result_mono _ ->
      failwith "action296 fixed hybrid: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 fixed hybrid: unexpected reference node";;

let candle_action296_fixed_hybrid_parent_domain =
  candle_action296_fixed_hybrid_find
    candle_action296_fixed_hybrid_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_fixed_hybrid_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_fixed_hybrid_parent_lower,
    candle_action296_fixed_hybrid_parent_upper =
  candle_action296_fixed_hybrid_domain_bounds
    candle_action296_fixed_hybrid_parent_domain;;

let _ =
  candle_action296_fixed_hybrid_marker
    "shared" "whole-box-source-preparation" "begin";;
let candle_action296_fixed_hybrid_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_fixed_hybrid_parent_lower
    candle_action296_fixed_hybrid_parent_upper;;
let _ =
  candle_action296_fixed_hybrid_marker
    "shared" "whole-box-source-preparation" "end";;

let _ =
  candle_action296_fixed_hybrid_marker
    "shared" "point-plan-compilation" "begin";;
let candle_action296_fixed_hybrid_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_action296_fixed_hybrid_box_prepared;;
let _ =
  candle_action296_fixed_hybrid_marker
    "shared" "point-plan-compilation" "end";;

let candle_action296_fixed_hybrid_left_domain,
    candle_action296_fixed_hybrid_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_fixed_hybrid_parent_domain;;

type candle_action296_fixed_hybrid_case = {
  candle_action296_fixed_hybrid_center_program: term;
  candle_action296_fixed_hybrid_boxes: term
};;

let candle_action296_fixed_hybrid_prepare_case domain_th =
  let lower,upper =
    candle_action296_fixed_hybrid_domain_bounds domain_th in
  let variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_fixed_hybrid_box_prepared
      candle_action296_fixed_hybrid_point_plan lower upper in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  if hyp boxes_representation <> [] then
    failwith "action296 fixed hybrid: box encoding assumptions";
  {candle_action296_fixed_hybrid_center_program =
     variant.variant_program_representation_term;
   candle_action296_fixed_hybrid_boxes = rand (concl boxes_representation)};;

let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "per-box-preparation" "begin";;
let candle_action296_fixed_hybrid_cases =
  map candle_action296_fixed_hybrid_prepare_case
    [candle_action296_fixed_hybrid_left_domain;
     candle_action296_fixed_hybrid_right_domain];;
let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "per-box-preparation" "end";;

let candle_action296_fixed_hybrid_case_term case =
  list_mk_comb
    (`Cexp_pair`,
     [case.candle_action296_fixed_hybrid_center_program;
      case.candle_action296_fixed_hybrid_boxes]);;

let candle_action296_fixed_hybrid_cases_term =
  itlist
    (fun case tail ->
      list_mk_comb
        (`Cexp_pair`,
         [candle_action296_fixed_hybrid_case_term case;tail]))
    candle_action296_fixed_hybrid_cases `Cexp_num 0`;;

let candle_action296_fixed_hybrid_box_program =
  candle_action296_fixed_hybrid_box_prepared.program_representation_term;;

let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "current-rational-complete-batch" "begin";;
let candle_action296_fixed_hybrid_current_batch =
  candle_action296_fixed_hybrid_compute
    candle_action296_fixed_hybrid_current_eqs
    (list_mk_comb
      (`candle_cv_action296_current_check_batch`,
       [candle_action296_fixed_hybrid_box_program;
        candle_action296_fixed_hybrid_cases_term]));;
let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "current-rational-complete-batch" "end";;

let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "fixed-hybrid-complete-batch" "begin";;
let candle_action296_fixed_hybrid_hybrid_batch =
  candle_action296_fixed_hybrid_compute
    candle_action296_fixed_hybrid_hybrid_eqs
    (list_mk_comb
      (`candle_cv_action296_fixed_hybrid_check_batch`,
       [candle_action296_fixed_hybrid_box_program;
        candle_action296_fixed_hybrid_cases_term]));;
let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "fixed-hybrid-complete-batch" "end";;

let candle_action296_fixed_hybrid_check_case equations checker case =
  candle_action296_fixed_hybrid_compute equations
    (list_mk_comb
      (checker,
       [case.candle_action296_fixed_hybrid_center_program;
        candle_action296_fixed_hybrid_box_program;
        case.candle_action296_fixed_hybrid_boxes]));;

let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "streamed-exact-comparison" "begin";;
let candle_action296_fixed_hybrid_exact =
  List.fold_left
    (fun count case ->
      let current =
        candle_action296_fixed_hybrid_check_case
          candle_cv_q_dim_taylor_model_certified_compute_eqs
          `candle_cv_q_dim_taylor_model_certified_check` case and
          hybrid =
            candle_action296_fixed_hybrid_check_case
              candle_cv_fs_q_dim_taylor_model_compute_eqs
              `candle_cv_fs_q_dim_taylor_model_certified_check` case in
      if hyp current <> [] || hyp hybrid <> [] ||
         not (aconv (rand (concl current)) (rand (concl hybrid))) then
        failwith "action296 fixed hybrid: complete result mismatch";
      count + 1)
    0 candle_action296_fixed_hybrid_cases;;
let _ =
  candle_action296_fixed_hybrid_marker
    "boxes-2" "streamed-exact-comparison" "end";;

let candle_action296_fixed_hybrid_axioms_after = axioms ();;

if length candle_action296_fixed_hybrid_cases <> 2 ||
   candle_action296_fixed_hybrid_exact <> 2 ||
   hyp candle_action296_fixed_hybrid_current_batch <> [] ||
   hyp candle_action296_fixed_hybrid_hybrid_batch <> [] ||
   not
     (aconv (rand (concl candle_action296_fixed_hybrid_current_batch))
       `Cexp_num 2`) ||
   not
     (aconv (rand (concl candle_action296_fixed_hybrid_hybrid_batch))
       `Cexp_num 2`) ||
   length candle_action296_fixed_hybrid_axioms_after <>
     length candle_action296_fixed_hybrid_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_hybrid_axioms_before)
       candle_action296_fixed_hybrid_axioms_after) then
  failwith "action296 fixed hybrid: final validation";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_HYBRID_RESULT cells=2" ^
   " shared_source_preparations=1 rational_batch_computes=1" ^
   " hybrid_batch_computes=1 exact_complete_outputs=2");;
print_endline
  "CANDLE_CV_ACTION296_FIXED_HYBRID_OK DEVELOPMENT_NON_RELEASE";;
