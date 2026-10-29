(* ========================================================================== *)
(* Explicit certificate streams for packed analytic source replay.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The earlier source-step relation deliberately *)
(* existentially quantifies nonlinear certificates.  A full executable entry *)
(* instead consumes concrete evidence.  This layer makes that consumption    *)
(* explicit while retaining exactly the same source semantics.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_program_object_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_packed_source_step_sound;;
open Candle_cv_analytic_expr_packed_source_program_sound;;
open Candle_cv_analytic_expr_packed_source_program_object_sound;;

(* Inverse consumes two intervals.  Square root consumes five.  Arctangent  *)
(* consumes the eight exact intervals occurring in its faithful source-step *)
(* contract.  All other instructions leave the stream untouched.            *)

let candle_q_packed_source_certificate_step_def = new_definition
 `candle_q_packed_source_certificate_step
      boxes source certificates stack next certificate_rest <=>
    (?item rest center_reciprocal box_reciprocal.
       source = Candle_analytic_program_inv /\
       certificates =
         CONS center_reciprocal (CONS box_reciprocal certificate_rest) /\
       stack = CONS item rest /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_reciprocal /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_reciprocal /\
       next =
         CONS
           (candle_q_packed_source_item_inv_certified boxes
             center_reciprocal box_reciprocal item) rest) \/
    (?source_sqrt item rest center_root box_root center_derivative
        box_derivative box_second_reciprocal.
       source = Candle_analytic_program_sqrt source_sqrt /\
       certificates =
         CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest)))) /\
       stack = CONS item rest /\
       candle_q_interval_sqrt_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item))) center_root /\
       candle_q_interval_inv_certificate
         (candle_q_interval_add_normalized center_root center_root)
         center_derivative /\
       candle_q_dim_jet_sqrt_certificates
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_root box_derivative box_second_reciprocal /\
       next =
         CONS
           (candle_q_packed_source_item_sqrt_certified boxes
             center_root box_root center_derivative box_derivative
             box_second_reciprocal item) rest) \/
    (?item rest center_input box_input center_result center_square
        center_derivative box_square box_derivative box_derivative_square.
       source = Candle_analytic_program_atn /\
       certificates =
         CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest))))))) /\
       stack = CONS item rest /\
       candle_q_interval_atn_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_input center_result /\
       candle_q_interval_square_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_input center_square /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_atn_denominator_with_square center_square)
         center_derivative /\
       candle_q_interval_square_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_input box_square /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_atn_denominator_with_square box_square)
         box_derivative /\
       candle_q_interval_square_outer_certificate
         box_derivative box_derivative box_derivative_square /\
       next =
         CONS
           (candle_q_packed_source_item_atn_faithful boxes
             center_input box_input center_result center_square
             center_derivative box_square box_derivative
             box_derivative_square item) rest) \/
    (~(source = Candle_analytic_program_inv) /\
     (!source_sqrt. ~(source = Candle_analytic_program_sqrt source_sqrt)) /\
     ~(source = Candle_analytic_program_atn) /\
     candle_q_packed_source_step boxes source stack next /\
     certificate_rest = certificates)`;;

let candle_q_packed_source_certificate_inverse_step_source_step = prove
 (`!boxes item rest center_reciprocal box_reciprocal.
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_reciprocal
     ==>
     candle_q_packed_source_step boxes Candle_analytic_program_inv
       (CONS item rest)
       (CONS
         (candle_q_packed_source_item_inv_certified boxes
           center_reciprocal box_reciprocal item) rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_source_certificate_sqrt_step_source_step = prove
 (`!boxes source_sqrt item rest center_root box_root center_derivative
       box_derivative box_second_reciprocal.
     candle_q_interval_sqrt_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item))) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized center_root center_root)
       center_derivative /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_root box_derivative box_second_reciprocal
     ==>
     candle_q_packed_source_step boxes
       (Candle_analytic_program_sqrt source_sqrt)
       (CONS item rest)
       (CONS
         (candle_q_packed_source_item_sqrt_certified boxes
           center_root box_root center_derivative box_derivative
           box_second_reciprocal item) rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_source_certificate_atn_step_source_step = prove
 (`!boxes item rest center_input box_input center_result center_square
       center_derivative box_square box_derivative box_derivative_square.
     candle_q_interval_atn_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_q_packed_source_step boxes Candle_analytic_program_atn
       (CONS item rest)
       (CONS
         (candle_q_packed_source_item_atn_faithful boxes
           center_input box_input center_result center_square
           center_derivative box_square box_derivative
           box_derivative_square item) rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  DISJ1_TAC THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_source_certificate_step_source_step = prove
 (`!boxes source certificates stack next certificate_rest.
     candle_q_packed_source_certificate_step
       boxes source certificates stack next certificate_rest
     ==>
     candle_q_packed_source_step boxes source stack next`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def] THEN
  MESON_TAC
    [candle_q_packed_source_certificate_inverse_step_source_step;
     candle_q_packed_source_certificate_sqrt_step_source_step;
     candle_q_packed_source_certificate_atn_step_source_step]);;

let candle_q_packed_source_certificate_program_run_def = define
 `(candle_q_packed_source_certificate_program_run
      boxes [] certificates stack result certificate_rest <=>
      result = stack /\ certificate_rest = certificates) /\
  (candle_q_packed_source_certificate_program_run
      boxes (CONS source sources) certificates stack result certificate_rest <=>
     ?next next_certificates.
       candle_q_packed_source_certificate_step
         boxes source certificates stack next next_certificates /\
       candle_q_packed_source_certificate_program_run
         boxes sources next_certificates next result certificate_rest)`;;

let candle_q_packed_source_certificate_program_run_source_run = prove
 (`!boxes sources certificates stack result certificate_rest.
     candle_q_packed_source_certificate_program_run
       boxes sources certificates stack result certificate_rest
     ==>
     candle_q_packed_source_program_run boxes sources stack result`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_certificate_program_run_def;
                candle_q_packed_source_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_certificate_program_run_def;
                candle_q_packed_source_program_run_def] THEN
    DISCH_THEN
      (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    USE_THEN "induction_hypothesis" MP_TAC THEN
    ASM_MESON_TAC
      [candle_q_packed_source_certificate_step_source_step]]);;

let candle_q_packed_source_certificate_program_run_analytic_invariant = prove
 (`!boxes sources certificates stack result certificate_rest.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_stack_analytic_invariant boxes stack /\
     candle_q_packed_source_certificate_program_run
       boxes sources certificates stack result certificate_rest
     ==>
     candle_q_packed_source_stack_analytic_invariant boxes result`,
  MESON_TAC
    [candle_q_packed_source_certificate_program_run_source_run;
     candle_q_packed_source_program_run_analytic_invariant]);;

let candle_q_packed_source_certificate_programs_object_invariant = prove
 (`!center_boxes outer_boxes center_sources outer_sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_certificate_program_run
       center_boxes center_sources center_certificates []
       (CONS center_item []) [] /\
     candle_q_packed_source_certificate_program_run
       outer_boxes outer_sources outer_certificates []
       (CONS outer_item []) [] /\
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_source_item_box_expr center_item) =
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr outer_item) /\
     candle_q_packed_hessian6_expand packed_hessian =
       candle_q_dim_taylor_model_result_hessian
         (candle_q_packed_source_item_result outer_item)
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result center_item) /\
        candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result outer_item))
       packed_hessian
       (candle_q_packed_source_item_box_expr center_item)
       (candle_q_packed_source_item_box_expr outer_item)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_source_programs_object_invariant THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `center_sources:candle_analytic_instruction list` THEN
  EXISTS_TAC `outer_sources:candle_analytic_instruction list` THEN
  CONJ_TAC THEN
  ASM_MESON_TAC
    [candle_q_packed_source_certificate_program_run_source_run]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_certificate_inverse_step_source_step;
     candle_q_packed_source_certificate_sqrt_step_source_step;
     candle_q_packed_source_certificate_atn_step_source_step;
     candle_q_packed_source_certificate_step_source_step;
     candle_q_packed_source_certificate_program_run_source_run;
     candle_q_packed_source_certificate_program_run_analytic_invariant;
     candle_q_packed_source_certificate_programs_object_invariant] then
  failwith "packed source certificate program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
