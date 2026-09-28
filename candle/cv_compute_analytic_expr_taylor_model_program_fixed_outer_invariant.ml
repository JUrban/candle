(* ========================================================================== *)
(* Universal analytic invariant for fixed-scale outer multiplication.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant = struct

open Multivariate_taylor;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
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

let candle_fso_accept label (th:thm) : tactic =
  fun (assumptions,goal) ->
    try ACCEPT_TAC th (assumptions,goal) with Failure _ ->
      print_endline (label ^ " expected:");
      print_term goal; print_newline ();
      print_endline (label ^ " theorem:");
      print_term (concl th); print_newline ();
      failwith label;;

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

let candle_fs_result_mul_analytic_box_hessian_contains = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left) center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right) center_b box_b /\
     candle_fs_result_domain left /\
     candle_fs_result_domain right /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian
         (candle_fs_result_mul
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           left right))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim
               (Candle_analytic_mul box_a box_b)) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q left)
      center_a box_a` in
  let right_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q right)
      center_b box_b` in
  let left_domain_th = ASSUME
    `candle_fs_result_domain
      (left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let right_domain_th = ASSUME
    `candle_fs_result_domain
      (right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let left_regular_th = MATCH_MP
   (ISPECL
     [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_box_regular)
   (CONJ left_invariant_th (CONJ left_domain_th point_th)) in
  let right_regular_th = MATCH_MP
   (ISPECL
     [`center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_box_regular)
   (CONJ right_invariant_th (CONJ right_domain_th point_th)) in
  let raw_hessian_th = MATCH_MP
   (ISPECL
     [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
      `box_a:candle_analytic_expr`;
      `center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
      `box_b:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_mul_analytic_hessian_contains)
   (end_itlist CONJ
     [REFL
       `candle_analytic_erase_sqrt_certificates box_a`;
      REFL
       `candle_analytic_erase_sqrt_certificates box_b`;
      left_invariant_th; right_invariant_th;
      left_domain_th; right_domain_th; point_th]) in
  REWRITE_TAC[candle_fs_result_mul_def;
              candle_fs_result_complete_raw_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_hessian_def;
              candle_fs_result_make_def; FST; SND] THEN
  MATCH_MP_TAC candle_fs_analytic_hessian_flyspeck_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_regular_at_def] THEN
    CONJ_TAC THENL
     [candle_fso_accept "fixed outer box: left regular" left_regular_th;
      candle_fso_accept "fixed outer box: right regular" right_regular_th];
    candle_fso_accept "fixed outer box: raw Hessian"
      (REWRITE_RULE[candle_fs_result_hessian_def] raw_hessian_th)]);;

let candle_fs_result_mul_analytic_center_contains = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left) center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right) center_b box_b /\
     candle_fs_result_domain left /\
     candle_fs_result_domain right
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center
           (candle_fs_result_mul
             (candle_fs_list_of_q
               (candle_q_fixed_list_round_upper
                 (candle_q_radius_list boxes)))
             left right))
         (candle_fs_result_hessian
           (candle_fs_result_mul
             (candle_fs_list_of_q
               (candle_q_fixed_list_round_upper
                 (candle_q_radius_list boxes)))
             left right)))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
       (Candle_analytic_mul center_a center_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q left)
      center_a box_a` in
  let right_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q right)
      center_b box_b` in
  let left_domain_th = ASSUME
    `candle_fs_result_domain
      (left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let right_domain_th = ASSUME
    `candle_fs_result_domain
      (right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let left_instance theorem = ISPECL
    [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`;
     `left:
       bool#
       (((num#num)#(num#num))#((num#num)#(num#num))list)#
       ((num#num)#(num#num))#
       ((num#num)#(num#num))list#
       (((num#num)#(num#num))list)list`;
     `type_witness:real^N`] theorem in
  let right_instance theorem = ISPECL
    [`center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`;
     `right:
       bool#
       (((num#num)#(num#num))#((num#num)#(num#num))list)#
       ((num#num)#(num#num))#
       ((num#num)#(num#num))list#
       (((num#num)#(num#num))list)list`;
     `type_witness:real^N`] theorem in
  let left_premises_th = CONJ left_invariant_th left_domain_th in
  let right_premises_th = CONJ right_invariant_th right_domain_th in
  let left_center_shape_th = MATCH_MP
    (left_instance candle_fs_result_analytic_center_shape)
    left_premises_th in
  let right_center_shape_th = MATCH_MP
    (right_instance candle_fs_result_analytic_center_shape)
    right_premises_th in
  let left_proxy_shape_th = MATCH_MP
    (left_instance candle_fs_result_analytic_proxy_data_shape)
    left_premises_th in
  let right_proxy_shape_th = MATCH_MP
    (right_instance candle_fs_result_analytic_proxy_data_shape)
    right_premises_th in
  let left_center_data_th =
    REWRITE_RULE[candle_fs_first_to_q_shape] left_center_shape_th in
  let right_center_data_th =
    REWRITE_RULE[candle_fs_first_to_q_shape] right_center_shape_th in
  let output_shape_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_center
        (left:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_center
        (right:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
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
          (((num#num)#(num#num))list)list)`]
     candle_fs_raw_mul_complete_shape)
   (end_itlist CONJ
     [CONJUNCT1 left_center_data_th;
      CONJUNCT1 right_center_data_th;
      CONJUNCT1 left_proxy_shape_th;
      CONJUNCT1 right_proxy_shape_th;
      CONJUNCT1 (CONJUNCT2 left_proxy_shape_th);
      CONJUNCT2 (CONJUNCT2 left_proxy_shape_th);
      CONJUNCT1 (CONJUNCT2 right_proxy_shape_th);
      CONJUNCT2 (CONJUNCT2 right_proxy_shape_th)]) in
  let left_value_th = MATCH_MP
    (left_instance candle_fs_result_analytic_center_value_contains)
    left_premises_th in
  let right_value_th = MATCH_MP
    (right_instance candle_fs_result_analytic_center_value_contains)
    right_premises_th in
  let left_gradient_th = MATCH_MP
    (left_instance candle_fs_result_analytic_center_gradient_contains)
    left_premises_th in
  let right_gradient_th = MATCH_MP
    (right_instance candle_fs_result_analytic_center_gradient_contains)
    right_premises_th in
  let center_value_gradient_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_fs_first_value
        (candle_fs_result_center
          (left:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_fs_first_value
        (candle_fs_result_center
          (right:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_fs_first_gradient
        (candle_fs_result_center
          (left:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_fs_first_gradient
        (candle_fs_result_center
          (right:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list))`;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_a`;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_b`;
      `(\i. candle_analytic_d i
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_a):num->real`;
      `(\i. candle_analytic_d i
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_b):num->real`]
     candle_fs_raw_mul_center_value_gradient_contains))
   (end_itlist CONJ
     [left_value_th; right_value_th;
      left_gradient_th; right_gradient_th]) in
  let center_domain_th = MATCH_MP candle_q_box_m_cell_domain
   (CONJ
     (ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`)
     (ASSUME `candle_q_box_valid_list boxes`)) in
  let center_in_box_th = MATCH_MP y_in_domain center_domain_th in
  let center_hessian_th = MATCH_MP
   (ISPECL
     [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
      `center_a:candle_analytic_expr`;
      `center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
      `center_b:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`;
      `(candle_q_box_center_vector boxes : real^N)`]
     candle_fs_result_mul_analytic_hessian_contains)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates center_a =
        candle_analytic_erase_sqrt_certificates box_a`;
      ASSUME
       `candle_analytic_erase_sqrt_certificates center_b =
        candle_analytic_erase_sqrt_certificates box_b`;
      left_invariant_th; right_invariant_th;
      left_domain_th; right_domain_th; center_in_box_th]) in
  REWRITE_TAC[candle_fs_result_mul_def;
              candle_fs_result_complete_raw_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_center_def;
              candle_fs_result_hessian_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              candle_fs_result_make_def; FST; SND;
              candle_q_dim_analytic_contains_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [candle_fso_accept "fixed outer center: shape"
      (REWRITE_RULE
        [candle_fs_result_center_def; candle_fs_result_hessian_def;
         candle_fs_first_make_def; candle_fs_first_value_def;
         candle_fs_first_gradient_def; FST; SND]
        output_shape_th);
    REWRITE_TAC[candle_analytic_value_def;
                candle_fs_first_value_def; FST; SND] THEN
    candle_fso_accept "fixed outer center: value"
      (REWRITE_RULE
        [candle_fs_result_center_def; candle_fs_first_value_def;
         candle_fs_first_gradient_def; FST; SND]
        (CONJUNCT1 center_value_gradient_th));
    REWRITE_TAC[candle_fso_analytic_mul_d_raw;
                candle_fs_first_gradient_def; FST; SND] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    candle_fso_accept "fixed outer center: gradient"
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE
          [candle_fs_result_center_def; candle_fs_first_value_def;
           candle_fs_first_gradient_def; FST; SND]
          (CONJUNCT2 center_value_gradient_th)));
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    candle_fso_accept "fixed outer center: Hessian"
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE[candle_fs_result_hessian_def]
          center_hessian_th))]);;

let candle_fs_result_mul_analytic_center_shape = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left) center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right) center_b box_b /\
     candle_fs_result_domain left /\
     candle_fs_result_domain right
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center
           (candle_fs_result_mul
             (candle_fs_list_of_q
               (candle_q_fixed_list_round_upper
                 (candle_q_radius_list boxes)))
             left right))
         (candle_fs_result_hessian
           (candle_fs_result_mul
             (candle_fs_list_of_q
               (candle_q_fixed_list_round_upper
                 (candle_q_radius_list boxes)))
             left right)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q left)
      center_a box_a` in
  let right_invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q right)
      center_b box_b` in
  let left_domain_th = ASSUME
    `candle_fs_result_domain
      (left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let right_domain_th = ASSUME
    `candle_fs_result_domain
      (right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let left_instance theorem = ISPECL
    [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`;
     `left:
       bool#
       (((num#num)#(num#num))#((num#num)#(num#num))list)#
       ((num#num)#(num#num))#
       ((num#num)#(num#num))list#
       (((num#num)#(num#num))list)list`;
     `type_witness:real^N`] theorem in
  let right_instance theorem = ISPECL
    [`center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`;
     `right:
       bool#
       (((num#num)#(num#num))#((num#num)#(num#num))list)#
       ((num#num)#(num#num))#
       ((num#num)#(num#num))list#
       (((num#num)#(num#num))list)list`;
     `type_witness:real^N`] theorem in
  let left_premises_th = CONJ left_invariant_th left_domain_th in
  let right_premises_th = CONJ right_invariant_th right_domain_th in
  let left_center_data_th = REWRITE_RULE[candle_fs_first_to_q_shape]
   (MATCH_MP (left_instance candle_fs_result_analytic_center_shape)
     left_premises_th) in
  let right_center_data_th = REWRITE_RULE[candle_fs_first_to_q_shape]
   (MATCH_MP (right_instance candle_fs_result_analytic_center_shape)
     right_premises_th) in
  let left_proxy_data_th = MATCH_MP
   (left_instance candle_fs_result_analytic_proxy_data_shape)
   left_premises_th in
  let right_proxy_data_th = MATCH_MP
   (right_instance candle_fs_result_analytic_proxy_data_shape)
   right_premises_th in
  REWRITE_TAC[candle_fs_result_mul_def;
              candle_fs_result_complete_raw_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_center_def;
              candle_fs_result_hessian_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              candle_fs_result_make_def; FST; SND] THEN
  MATCH_MP_TAC
    (REWRITE_RULE
      [candle_fs_first_make_def; candle_fs_first_value_def;
       candle_fs_first_gradient_def; FST; SND]
      candle_fs_raw_mul_complete_shape) THEN
  candle_fso_accept "fixed outer center shape: dimensions"
   (REWRITE_RULE
     [candle_fs_result_center_def; candle_fs_result_hessian_def;
      candle_fs_first_gradient_def; FST; SND]
      (end_itlist CONJ
       [CONJUNCT1 left_center_data_th;
        CONJUNCT1 right_center_data_th;
        CONJUNCT1 left_proxy_data_th;
        CONJUNCT1 right_proxy_data_th;
        CONJUNCT1 (CONJUNCT2 left_proxy_data_th);
        CONJUNCT2 (CONJUNCT2 left_proxy_data_th);
        CONJUNCT1 (CONJUNCT2 right_proxy_data_th);
        CONJUNCT2 (CONJUNCT2 right_proxy_data_th)])));;

let candle_fs_result_mul_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left) center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right) center_b box_b
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fs_result_mul
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           left right))
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
   (fun right_th ->
      POP_ASSUM
       (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_fs_result_mul_def;
              candle_fs_result_complete_raw_def] THEN
  ASM_CASES_TAC
   `candle_fs_result_domain
      (left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list) /\
    candle_fs_result_domain
      (right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      USE_THEN "left_invariant"
       (fun left_invariant_th ->
          USE_THEN "right_invariant"
           (fun right_invariant_th ->
              let domains_th = ASSUME
               `candle_fs_result_domain
                  (left:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list) /\
                candle_fs_result_domain
                  (right:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list)` in
              let left_domain_th,right_domain_th = CONJ_PAIR domains_th in
              let left_enabled_th = MATCH_MP
               (REWRITE_RULE
                 [candle_q_dim_taylor_model_result_analytic_invariant_def;
                  candle_fs_result_to_q_domain]
                 left_invariant_th)
               left_domain_th in
              let right_enabled_th = MATCH_MP
               (REWRITE_RULE
                 [candle_q_dim_taylor_model_result_analytic_invariant_def;
                  candle_fs_result_to_q_domain]
                 right_invariant_th)
               right_domain_th in
              let left_center_regular_th,left_rest =
                CONJ_PAIR left_enabled_th in
              let left_box_regular_th,_ = CONJ_PAIR left_rest in
              let right_center_regular_th,right_rest =
                CONJ_PAIR right_enabled_th in
              let right_box_regular_th,_ = CONJ_PAIR right_rest in
              let center_shape_th = MATCH_MP
               (ISPECL
                 [`center_a:candle_analytic_expr`;
                  `center_b:candle_analytic_expr`;
                  `box_a:candle_analytic_expr`;
                  `box_b:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `left:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `right:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `type_witness:real^N`]
                 candle_fs_result_mul_analytic_center_shape)
               (CONJ left_invariant_th
                 (CONJ right_invariant_th
                   (CONJ left_domain_th right_domain_th))) in
              let center_contains_th = MATCH_MP
               (ISPECL
                 [`center_a:candle_analytic_expr`;
                  `center_b:candle_analytic_expr`;
                  `box_a:candle_analytic_expr`;
                  `box_b:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `left:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `right:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `type_witness:real^N`]
                 candle_fs_result_mul_analytic_center_contains)
               (end_itlist CONJ
                 [ASSUME
                   `candle_analytic_erase_sqrt_certificates center_a =
                    candle_analytic_erase_sqrt_certificates box_a`;
                  ASSUME
                   `candle_analytic_erase_sqrt_certificates center_b =
                    candle_analytic_erase_sqrt_certificates box_b`;
                  ASSUME
                   `LENGTH
                     (boxes:(((num#num)#num)#((num#num)#num))list) =
                    dimindex (:N)`;
                  ASSUME `candle_q_box_valid_list boxes`;
                  left_invariant_th; right_invariant_th;
                  left_domain_th; right_domain_th]) in
              let p = `p:real^N` in
              let point_property =
               `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]` in
              let box_point_th = MATCH_MP
               (ISPECL
                 [`center_a:candle_analytic_expr`;
                  `center_b:candle_analytic_expr`;
                  `box_a:candle_analytic_expr`;
                  `box_b:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `left:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `right:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `type_witness:real^N`; p]
                 candle_fs_result_mul_analytic_box_hessian_contains)
               (end_itlist CONJ
                 [ASSUME
                   `candle_analytic_valid_dim (dimindex (:N)) box_a`;
                  ASSUME
                   `candle_analytic_valid_dim (dimindex (:N)) box_b`;
                  left_invariant_th; right_invariant_th;
                  left_domain_th; right_domain_th;
                  ASSUME point_property]) in
              let box_all_th = GEN p
                (DISCH point_property box_point_th) in
              EVERY
               [candle_fsa_label_instantiated
                  "left_center_regular" left_center_regular_th;
                candle_fsa_label_instantiated
                  "right_center_regular" right_center_regular_th;
                candle_fsa_label_instantiated
                  "left_box_regular" left_box_regular_th;
                candle_fsa_label_instantiated
                  "right_box_regular" right_box_regular_th;
                candle_fsa_label_instantiated
                  "mul_center_shape" center_shape_th;
                candle_fsa_label_instantiated
                  "mul_center_contains" center_contains_th;
                candle_fsa_label_instantiated
                  "mul_box_hessian_all" box_all_th])) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[candle_analytic_regular_at_def] THEN
        CONJ_TAC THENL
         [USE_THEN "left_center_regular" ACCEPT_TAC;
          USE_THEN "right_center_regular" ACCEPT_TAC];
        X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        REWRITE_TAC[candle_analytic_regular_at_def] THEN
        CONJ_TAC THENL
         [USE_THEN "left_box_regular"
           (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
          ASM_REWRITE_TAC[];
          USE_THEN "right_box_regular"
           (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
          ASM_REWRITE_TAC[]];
        USE_THEN "mul_center_shape"
         (fun th ->
            REWRITE_TAC[candle_fs_result_center_def;
                        candle_fs_result_hessian_def] THEN
            candle_fso_accept "fixed outer invariant: center shape"
             (REWRITE_RULE
               [candle_fs_result_mul_def;
                candle_fs_result_complete_raw_def;
                candle_fs_result_complete_rounded_def;
                candle_fs_result_center_def;
                candle_fs_result_hessian_def;
                candle_fs_result_make_def; FST; SND]
               th));
        USE_THEN "mul_center_contains"
         (fun th ->
            REWRITE_TAC[candle_fs_result_center_def;
                        candle_fs_result_hessian_def] THEN
            candle_fso_accept "fixed outer invariant: center contains"
             (REWRITE_RULE
               [candle_fs_result_mul_def;
                candle_fs_result_complete_raw_def;
                candle_fs_result_complete_rounded_def;
                candle_fs_result_center_def;
                candle_fs_result_hessian_def;
                candle_fs_result_make_def; FST; SND]
               th));
        X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        USE_THEN "mul_box_hessian_all"
         (fun th ->
            MP_TAC
             (MATCH_MP (SPEC `p:real^N` th)
               (ASSUME
                 `(p:real^N) IN interval
                   [candle_q_box_lower_vector boxes,
                    candle_q_box_upper_vector boxes]`))) THEN
        REWRITE_TAC[candle_fs_result_mul_def;
                    candle_fs_result_complete_raw_def;
                    candle_fs_result_complete_rounded_def;
                    candle_fs_result_hessian_def;
                    candle_fs_result_make_def; FST; SND]]];
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
                candle_fs_result_to_q_domain;
                candle_fs_result_complete_domain] THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_result_square_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fs_result_square
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           result))
       (Candle_analytic_square center_e)
       (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_square_def] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes
      (candle_fs_result_to_q
        (candle_fs_result_mul
          (candle_fs_list_of_q
            (candle_q_fixed_list_round_upper
              (candle_q_radius_list boxes)))
          result result))
      (Candle_analytic_mul center_e center_e)
      (Candle_analytic_mul box_e box_e)`
   MP_TAC THENL
   [MATCH_MP_TAC candle_fs_result_mul_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
                candle_analytic_regular_at_def;
                candle_q_dim_analytic_contains_def;
                candle_analytic_value_def;
                candle_analytic_d_def;
                candle_analytic_dd_def]]);;

end;;
