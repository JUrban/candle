(* ========================================================================== *)
(* Universal analytic invariant for fixed-scale outer multiplication.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant = struct

open Multivariate_taylor;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_hessian;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;

let candle_fso_analytic_mul_d_raw = prove
 (`!i env left right.
     candle_analytic_d i env (Candle_analytic_mul left right) =
     candle_analytic_value env right * candle_analytic_d i env left +
     candle_analytic_value env left * candle_analytic_d i env right`,
  REWRITE_TAC[candle_analytic_d_def] THEN REAL_ARITH_TAC);;

let candle_fso_analytic_mul_dd_raw = prove
 (`!i j env left right.
     candle_analytic_dd i j env (Candle_analytic_mul left right) =
     (candle_analytic_value env right *
        candle_analytic_dd i j env left +
      candle_analytic_d i env left * candle_analytic_d j env right) +
     (candle_analytic_d i env right * candle_analytic_d j env left +
      candle_analytic_value env left *
        candle_analytic_dd i j env right)`,
  REWRITE_TAC[candle_analytic_dd_def] THEN REAL_ARITH_TAC);;

(* Expose every fixed proxy component at a point.  [target_e] may be either  *)
(* certificate-decorated source, provided it has the authenticated erased    *)
(* identity of the box expression.                                           *)

let candle_fs_result_analytic_proxy_target_components = prove
 (`!center_e box_e target_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_erase_sqrt_certificates target_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_fs_interval_contains
       (candle_fs_result_value_bound result)
       (candle_analytic_value
         (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) target_e) /\
     ALL2 candle_fs_interval_contains
       (candle_fs_result_gradient_bounds result)
       (list_of_seq
         (\di. candle_analytic_d di
           (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) target_e)
         (dimindex (:N))) /\
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian result)
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) target_e)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let proxy_shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_shape)
   (CONJ invariant_th domain_th) in
  let enabled_th = MATCH_MP
   (REWRITE_RULE
     [candle_q_dim_taylor_model_result_analytic_invariant_def;
      candle_fs_result_to_q_domain]
     invariant_th)
   domain_th in
  let _,rest1 = CONJ_PAIR enabled_th in
  let _,rest2 = CONJ_PAIR rest1 in
  let _,rest3 = CONJ_PAIR rest2 in
  let _,rest4 = CONJ_PAIR rest3 in
  let _,box_contains_all_th = CONJ_PAIR rest4 in
  let box_contains_th = MATCH_MP (SPEC `p:real^N` box_contains_all_th)
    point_th in
  let transport_equiv = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      `candle_q_dim_taylor_model_proxy
        (candle_fs_result_to_q
          (result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))`;
      `target_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
     candle_q_dim_analytic_contains_certificate_transport)
   (ASSUME
     `candle_analytic_erase_sqrt_certificates target_e =
      candle_analytic_erase_sqrt_certificates box_e`) in
  let target_contains_th = MATCH_MP (snd (EQ_IMP_RULE transport_equiv))
    box_contains_th in
  let components_th = REWRITE_RULE[candle_q_dim_analytic_contains_def]
    target_contains_th in
  let value_th = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def] components_th) in
  let gradient_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      `candle_q_dim_taylor_model_proxy
        (candle_fs_result_to_q
          (result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) target_e`;
      `(\di. candle_analytic_d di
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->num->real`]
     candle_q_dim_jet_components_gradient_contains)
   (CONJ proxy_shape_th components_th) in
  let hessian_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      `candle_q_dim_taylor_model_proxy
        (candle_fs_result_to_q
          (result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) target_e`;
      `(\di. candle_analytic_d di
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->num->real`]
     candle_q_dim_jet_components_hessian_contains)
   (CONJ proxy_shape_th components_th) in
  REPEAT CONJ_TAC THENL
   [MP_TAC value_th THEN
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_fs_result_to_q_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_value_bound_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                candle_fs_interval_to_q_contains; FST; SND];
    MP_TAC gradient_th THEN
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_fs_result_to_q_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_gradient_bounds_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
                candle_fs_interval_list_to_q_contains; FST; SND];
    MP_TAC hessian_th THEN
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_fs_result_to_q_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_hessian_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
                candle_fs_interval_matrix_to_q_contains; FST; SND]]);;

(* The fixed multiplication Hessian formula is valid for arbitrary analytic  *)
(* operands, not merely the polynomial fragment for which it was first used. *)

let candle_fs_result_mul_analytic_hessian_contains = prove
 (`!left_center left_box left_target
      right_center right_box right_target boxes left right
      (type_witness:real^N) (p:real^N).
     candle_analytic_erase_sqrt_certificates left_target =
       candle_analytic_erase_sqrt_certificates left_box /\
     candle_analytic_erase_sqrt_certificates right_target =
       candle_analytic_erase_sqrt_certificates right_box /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left)
       left_center left_box /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right)
       right_center right_box /\
     candle_fs_result_domain left /\
     candle_fs_result_domain right /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_raw_interval_matrix_round candle_fs_scale
         (candle_fs_raw_interval_matrix_add
           (candle_fs_raw_interval_matrix_add
             (candle_fs_raw_interval_matrix_scale
               (candle_fs_result_value_bound right)
               (candle_fs_result_hessian left))
             (candle_fs_raw_interval_outer
               (candle_fs_result_gradient_bounds left)
               (candle_fs_result_gradient_bounds right)))
           (candle_fs_raw_interval_matrix_add
             (candle_fs_raw_interval_outer
               (candle_fs_result_gradient_bounds right)
               (candle_fs_result_gradient_bounds left))
             (candle_fs_raw_interval_matrix_scale
               (candle_fs_result_value_bound left)
               (candle_fs_result_hessian right)))))
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
             (Candle_analytic_mul left_target right_target))
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_components_th = MATCH_MP
   (ISPECL
     [`left_center:candle_analytic_expr`; `left_box:candle_analytic_expr`;
      `left_target:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates left_target =
        candle_analytic_erase_sqrt_certificates left_box`;
      ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes (candle_fs_result_to_q left)
         left_center left_box`;
      ASSUME
       `candle_fs_result_domain
         (left:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`;
      ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`]) in
  let right_components_th = MATCH_MP
   (ISPECL
     [`right_center:candle_analytic_expr`; `right_box:candle_analytic_expr`;
      `right_target:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates right_target =
        candle_analytic_erase_sqrt_certificates right_box`;
      ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes (candle_fs_result_to_q right)
         right_center right_box`;
      ASSUME
       `candle_fs_result_domain
         (right:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`;
      ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`]) in
  let left_value_th,left_rest = CONJ_PAIR left_components_th in
  let left_gradient_th,left_hessian_th = CONJ_PAIR left_rest in
  let right_value_th,right_rest = CONJ_PAIR right_components_th in
  let right_gradient_th,right_hessian_th = CONJ_PAIR right_rest in
  let left_shape_th = MATCH_MP
   (ISPECL
     [`left_center:candle_analytic_expr`; `left_box:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes (candle_fs_result_to_q left)
         left_center left_box`)
     (ASSUME
       `candle_fs_result_domain
         (left:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let right_shape_th = MATCH_MP
   (ISPECL
     [`right_center:candle_analytic_expr`; `right_box:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes (candle_fs_result_to_q right)
         right_center right_box`)
     (ASSUME
       `candle_fs_result_domain
         (right:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let raw_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_value_bound
        (left:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_value_bound
        (right:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_gradient_bounds
        (left:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_gradient_bounds
        (right:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_hessian
        (left:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_hessian
        (right:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        left_target`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        right_target`;
      `(\i. candle_analytic_d i
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        left_target):num->real`;
      `(\i. candle_analytic_d i
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        right_target):num->real`;
      `(\i j. candle_analytic_dd i j
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        left_target):num->num->real`;
      `(\i j. candle_analytic_dd i j
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        right_target):num->num->real`]
     candle_fs_raw_mul_hessian_contains))
   (end_itlist CONJ
     [left_value_th; right_value_th;
      left_gradient_th; right_gradient_th;
      left_hessian_th; right_hessian_th;
      CONJUNCT1 left_shape_th; CONJUNCT1 right_shape_th;
      CONJUNCT1 (CONJUNCT2 left_shape_th);
      CONJUNCT2 (CONJUNCT2 left_shape_th);
      CONJUNCT1 (CONJUNCT2 right_shape_th);
      CONJUNCT2 (CONJUNCT2 right_shape_th)]) in
  MP_TAC raw_th THEN
  REWRITE_TAC[candle_fso_analytic_mul_dd_raw]);;

(* Convert the zero-based analytic Hessian view used by the reflected       *)
(* evaluator to the one-based [partial2] view consumed by Flyspeck Taylor.  *)

let candle_fs_analytic_hessian_flyspeck_contains = prove
 (`!e hessian (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e)
           (dimindex (:N)))
         (dimindex (:N)))
     ==>
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim e) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `list_of_seq
      (\di. list_of_seq
        (\dj. partial2 (dj + 1) (di + 1)
          (candle_analytic_denote_dim e) (p:real^N))
        (dimindex (:N)))
      (dimindex (:N)) =
    list_of_seq
      (\di. list_of_seq
        (\dj. candle_analytic_dd di dj
          (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e)
        (dimindex (:N)))
      (dimindex (:N))`
   SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `di:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `dj:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    MP_TAC
     (ISPECL
       [`e:candle_analytic_expr`; `p:real^N`; `di + 1`; `dj + 1`]
       candle_analytic_denote_dim_second_partial) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`;
                  ARITH_RULE `(dj + 1) - 1 = dj`]];
    ASM_REWRITE_TAC[]]);;

end;;
