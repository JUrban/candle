(* ========================================================================== *)
(* Direct analytic soundness of the packed object-q pi/2 state.             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast fixed-word checker retains the       *)
(* authenticated binary pi/2 interval directly.  The older exact source      *)
(* replay completes and rounds that interval at decimal scale 10^12, so the   *)
(* two sound intervals need not enclose one another.  This theorem proves the *)
(* semantic property needed by the packed-object bridge without imposing that *)
(* invalid representation-order requirement.                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_invariant.ml";;

module Candle_cv_analytic_expr_packed_source_object_pi_half_sound = struct

open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;

let candle_q_packed_object_zero_gradient6_def = new_definition
 `candle_q_packed_object_zero_gradient6 =
    [candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval]`;;

let candle_q_packed_object_zero_hessian21_def = new_definition
 `candle_q_packed_object_zero_hessian21 =
    [candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval; candle_q_zero_interval;
     candle_q_zero_interval]`;;

let candle_q_packed_object_zero_matrix6_def = new_definition
 `candle_q_packed_object_zero_matrix6 =
    [[candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval];
     [candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval];
     [candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval];
     [candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval];
     [candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval];
     [candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval;
      candle_q_zero_interval; candle_q_zero_interval]]`;;

(* [bounded_atan_pi_half] decoded by the HOL4 object-q refinement.  The two  *)
(* endpoints share the runtime scale 2^40 and are intentionally left in that *)
(* unnormalised representation here.                                         *)

let candle_q_packed_object_pi_half_scale40_interval_def = new_definition
 `candle_q_packed_object_pi_half_scale40_interval =
    ((((1727108826112,0),1099511627775),
      ((1727108826368,0),1099511627775)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_packed_object_pi_half_scale40_interval_sound = prove
 (`candle_q_interval_contains
     candle_q_packed_object_pi_half_scale40_interval (pi / &2)`,
  MP_TAC candle_q_pi_half_interval_sound THEN
  REWRITE_TAC[candle_q_packed_object_pi_half_scale40_interval_def;
              candle_q_pi_half_interval_def;
              candle_q_interval_contains_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let candle_q_packed_object_zero_gradient6_length = prove
 (`LENGTH candle_q_packed_object_zero_gradient6 = 6`,
  REWRITE_TAC[candle_q_packed_object_zero_gradient6_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_zero_hessian21_length = prove
 (`LENGTH candle_q_packed_object_zero_hessian21 = 21`,
  REWRITE_TAC[candle_q_packed_object_zero_hessian21_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_zero_gradient6_lookup = prove
 (`!i. i < 6
       ==> candle_q_interval_lookup i
             candle_q_packed_object_zero_gradient6 =
           candle_q_zero_interval`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (ARITH_RULE
      `i < 6 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_zero_gradient6_def;
              num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`;
              candle_q_interval_lookup_def]);;

let candle_q_packed_object_zero_hessian6_expand = prove
 (`candle_q_packed_hessian6_expand
      candle_q_packed_object_zero_hessian21 =
    candle_q_packed_object_zero_matrix6`,
  REWRITE_TAC[candle_q_packed_hessian6_expand_def;
              candle_q_packed_object_zero_hessian21_def;
              candle_q_packed_object_zero_matrix6_def] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let candle_q_packed_object_zero_hessian6_lookup = prove
 (`!i j. i < 6 /\ j < 6
         ==> candle_q_interval_lookup j
               (candle_q_dim_interval_row_lookup i
                 (candle_q_packed_hessian6_expand
                   candle_q_packed_object_zero_hessian21)) =
             candle_q_zero_interval`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `i < 6 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  MP_TAC
    (ARITH_RULE
      `j < 6 ==> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_zero_hessian6_expand;
              candle_q_packed_object_zero_matrix6_def;
              num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`;
              candle_q_dim_interval_row_lookup_def;
              candle_q_interval_lookup_def] THEN
  CONV_TAC (DEPTH_CONV EL_CONV));;

let candle_q_packed_object_pi_half_interval_center_contains = prove
 (`!pi_interval environment.
     candle_q_interval_contains pi_interval (pi / &2)
     ==>
     candle_q_packed_object_center_first_contains
       pi_interval
       candle_q_packed_object_zero_gradient6
       environment Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_gradient6_lookup;
                 candle_q_zero_interval_contains]]);;

let candle_q_packed_object_pi_half_interval_box_contains = prove
 (`!pi_interval environment.
     candle_q_interval_contains pi_interval (pi / &2)
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         pi_interval
         candle_q_packed_object_zero_gradient6
         candle_q_packed_object_zero_hessian21)
       environment Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_gradient6_lookup;
                 candle_q_zero_interval_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_hessian6_lookup;
                 candle_q_zero_interval_contains]]);;

let candle_q_packed_object_pi_half_interval_analytic_invariant = prove
 (`!center_boxes outer_boxes pi_interval.
     candle_q_interval_contains pi_interval (pi / &2)
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes T
       pi_interval
       candle_q_packed_object_zero_gradient6
       pi_interval
       candle_q_packed_object_zero_gradient6
       candle_q_packed_object_zero_hessian21
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_packed_object_zero_gradient6_length];
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_hessian_def;
                candle_q_dim_jet_make_def;
                candle_q_dim_interval_matrix_shape_def;
                candle_q_dim_interval_rows_width_all; FST; SND] THEN
    REWRITE_TAC[candle_q_packed_object_zero_gradient6_length;
                candle_q_packed_hessian6_expand_shape];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_pi_half_interval_center_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_pi_half_interval_box_contains]]);;

let candle_q_packed_object_pi_half_analytic_invariant = prove
 (`!center_boxes outer_boxes.
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes T
       candle_q_pi_half_interval
       candle_q_packed_object_zero_gradient6
       candle_q_pi_half_interval
       candle_q_packed_object_zero_gradient6
       candle_q_packed_object_zero_hessian21
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `candle_q_pi_half_interval`]
      candle_q_packed_object_pi_half_interval_analytic_invariant) THEN
  MATCH_ACCEPT_TAC candle_q_pi_half_interval_sound);;

let candle_q_packed_object_pi_half_scale40_analytic_invariant = prove
 (`!center_boxes outer_boxes.
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes T
       candle_q_packed_object_pi_half_scale40_interval
       candle_q_packed_object_zero_gradient6
       candle_q_packed_object_pi_half_scale40_interval
       candle_q_packed_object_zero_gradient6
       candle_q_packed_object_zero_hessian21
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `candle_q_packed_object_pi_half_scale40_interval`]
      candle_q_packed_object_pi_half_interval_analytic_invariant) THEN
  MATCH_ACCEPT_TAC
    candle_q_packed_object_pi_half_scale40_interval_sound);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_zero_gradient6_length;
     candle_q_packed_object_zero_hessian21_length;
     candle_q_packed_object_pi_half_scale40_interval_sound;
     candle_q_packed_object_zero_gradient6_lookup;
     candle_q_packed_object_zero_hessian6_expand;
     candle_q_packed_object_zero_hessian6_lookup;
     candle_q_packed_object_pi_half_interval_center_contains;
     candle_q_packed_object_pi_half_interval_box_contains;
     candle_q_packed_object_pi_half_interval_analytic_invariant;
     candle_q_packed_object_pi_half_analytic_invariant;
     candle_q_packed_object_pi_half_scale40_analytic_invariant] then
  failwith "packed source object pi-half sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_PI_HALF_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
