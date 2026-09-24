(* ========================================================================== *)
(* Analytic soundness of the shared dimension-generic polynomial jets.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A center jet supplies the Taylor value and    *)
(* gradient.  A separately evaluated full-box jet supplies the Hessian       *)
(* enclosure.  The general Flyspeck Taylor theorem then bounds the source    *)
(* expression without constructing per-expression derivative theorems.       *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_check.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_sound.ml";;

module Candle_cv_polynomial_expr_dim_jet_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_jet_check;;

let candle_q_dim_jet_gradient_list_of_seq = prove
 (`!n jet.
     candle_q_dim_jet_shape n jet
     ==>
     candle_q_dim_jet_gradient jet =
     list_of_seq (\i. candle_q_dim_jet_gradient_at jet i) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def] THEN STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_q_dim_jet_gradient_at_def;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_jet_hessian_row_list_of_seq = prove
 (`!n jet i.
     candle_q_dim_jet_shape n jet /\ i < n
     ==>
     candle_q_dim_interval_row_lookup i
       (candle_q_dim_jet_hessian jet) =
     list_of_seq (\j. candle_q_dim_jet_hessian_at jet i j) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_dim_interval_row_lookup i
        (candle_q_dim_jet_hessian jet)) = n`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_interval_rows_width_lookup_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_q_dim_jet_hessian_at_def;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_jet_hessian_list_of_seq = prove
 (`!n jet.
     candle_q_dim_jet_shape n jet
     ==>
     candle_q_dim_jet_hessian jet =
     list_of_seq
       (\i. list_of_seq
         (\j. candle_q_dim_jet_hessian_at jet i j) n)
       n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_interval_matrix_shape_def];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ASM_MESON_TAC[candle_q_dim_jet_hessian_row_list_of_seq;
                candle_q_dim_interval_row_lookup_in_range;
                candle_q_dim_jet_shape_def;
                candle_q_dim_interval_matrix_shape_def]);;

let candle_q_dim_poly_jet_gradient_contains = prove
 (`!n jet env e.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_poly_jet_contains n jet env e
     ==>
     candle_q_stack_contains
       (candle_q_dim_jet_gradient jet)
       (candle_poly_gradient n env e)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_gradient jet =
    list_of_seq (\i. candle_q_dim_jet_gradient_at jet i) n`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_gradient_list_of_seq THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_poly_gradient_def;
                candle_all2_list_of_seq] THEN
    ASM_MESON_TAC[candle_q_dim_poly_jet_contains_def]]);;

let candle_q_dim_poly_jet_hessian_contains = prove
 (`!n jet env e.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_poly_jet_contains n jet env e
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian jet)
       (candle_poly_hessian n env e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_hessian jet =
    list_of_seq
      (\i. list_of_seq
        (\j. candle_q_dim_jet_hessian_at jet i j) n)
      n`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_hessian_list_of_seq THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_poly_hessian_def;
                candle_all2_list_of_seq] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[candle_q_stack_contains_all2;
                candle_all2_list_of_seq] THEN
    ASM_MESON_TAC[candle_q_dim_poly_jet_contains_def]]);;

let candle_q_dim_poly_jet_gradient_flyspeck_contains = prove
 (`!e boxes center_jet.
     candle_poly_valid_dim (dimindex (:N)) e /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_poly_jet_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e
     ==>
     candle_q_stack_contains
       (candle_q_dim_jet_gradient center_jet)
       (list_of_seq
         (\di. partial (di + 1) (candle_poly_denote_dim e)
           (candle_q_box_center_vector boxes : real^N))
         (dimindex (:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`e:candle_poly_expr`;
      `(candle_q_box_center_vector boxes : real^N)`]
     candle_poly_gradient_flyspeck_partials) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC candle_q_dim_poly_jet_gradient_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dim_poly_jet_hessian_flyspeck_contains = prove
 (`!e box_jet (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     candle_q_dim_poly_jet_contains (dimindex (:N)) box_jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian box_jet)
       (list_of_seq
         (\di.
            list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e) (z:real^N))
              (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (ISPECL [`e:candle_poly_expr`; `z:real^N`]
     candle_poly_hessian_flyspeck_partials) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC candle_q_dim_poly_jet_hessian_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dim_jet_gradient_taylor_sum_bound = prove
 (`!e boxes center_jet.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_poly_jet_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs
              (partial i (candle_poly_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_gradient center_jet))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_dim_jet_gradient center_jet)
      (list_of_seq
        (\di. partial (di + 1) (candle_poly_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N)))`
   (LABEL_TAC "gradient_contains") THENL
   [MATCH_MP_TAC candle_q_dim_poly_jet_gradient_flyspeck_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial i (candle_poly_denote_dim e)
               (candle_q_box_center_vector boxes : real^N))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial ((i - 1) + 1) (candle_poly_denote_dim e)
               (candle_q_box_center_vector boxes : real^N)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)`
   (LABEL_TAC "radii_nonnegative") THENL
   [MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_radius_list boxes) =
    LENGTH
      (list_of_seq
        (\di. partial (di + 1) (candle_poly_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N)))`
   (LABEL_TAC "radius_gradient_lengths") THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let sound_th =
    SPECL
     [`candle_q_radius_list boxes`;
      `list_of_seq
        (\di. partial (di + 1) (candle_poly_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))`;
      `candle_q_dim_jet_gradient center_jet`]
     candle_q_dot_abs_upper_sound in
  let bound_th =
    MATCH_MP sound_th
      (CONJ
        (ASSUME
          `ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)`)
        (CONJ
          (ASSUME
            `candle_q_stack_contains
              (candle_q_dim_jet_gradient center_jet)
              (list_of_seq
                (\di. partial (di + 1) (candle_poly_denote_dim e)
                  (candle_q_box_center_vector boxes : real^N))
                (dimindex (:N)))`)
          (ASSUME
            `LENGTH (candle_q_radius_list boxes) =
             LENGTH
               (list_of_seq
                 (\di. partial (di + 1) (candle_poly_denote_dim e)
                   (candle_q_box_center_vector boxes : real^N))
                 (dimindex (:N)))`))) in
  let sum_imp =
    ISPECL
     [`boxes:(((num#num)#num)#((num#num)#num))list`;
      `\di. partial (di + 1) (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)`]
     candle_q_dot_list_of_seq_sum in
  let boxes_length_th =
    ASSUME
     `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
      dimindex (:N)` in
  let sum_th = BETA_RULE (MATCH_MP sum_imp boxes_length_th) in
  ONCE_REWRITE_TAC[GSYM sum_th] THEN
  ACCEPT_TAC bound_th);;

let candle_q_dim_jet_hessian_taylor_sum_bound = prove
 (`!e boxes box_jet (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     candle_q_dim_poly_jet_contains (dimindex (:N)) box_jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                   abs
                     (partial2 j i (candle_poly_denote_dim e) (z:real^N)))) <=
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_hessian box_jet))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_q_stack_contains
      (candle_q_dim_jet_hessian box_jet)
      (list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_contains") THENL
   [MATCH_MP_TAC candle_q_dim_poly_jet_hessian_flyspeck_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs (partial2 j i (candle_poly_denote_dim e) (z:real^N)))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs
                    (partial2 ((j - 1) + 1) ((i - 1) + 1)
                      (candle_poly_denote_dim e) (z:real^N))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)`
   (LABEL_TAC "hessian_radii_nonnegative") THENL
   [MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_radius_list boxes) =
    LENGTH
      (list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_outer_lengths") THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL
      (\values. LENGTH (candle_q_radius_list boxes) = LENGTH values)
      (list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_row_lengths") THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC[candle_q_radius_list_length;
                 EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let sound_th =
    SPECL
     [`candle_q_radius_list boxes`;
      `candle_q_radius_list boxes`;
      `list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N))`;
      `candle_q_dim_jet_hessian box_jet`]
     candle_q_weighted_rows_abs_upper_sound in
  let radii_th =
    ASSUME
     `ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)` in
  let contains_th =
    ASSUME
     `ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian box_jet)
       (list_of_seq
         (\di.
            list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e) (z:real^N))
              (dimindex (:N)))
         (dimindex (:N)))` in
  let outer_lengths_th =
    ASSUME
     `LENGTH (candle_q_radius_list boxes) =
      LENGTH
        (list_of_seq
          (\di.
             list_of_seq
               (\dj. partial2 (dj + 1) (di + 1)
                 (candle_poly_denote_dim e) (z:real^N))
               (dimindex (:N)))
          (dimindex (:N)))` in
  let row_lengths_th =
    ASSUME
     `ALL
       (\values. LENGTH (candle_q_radius_list boxes) = LENGTH values)
       (list_of_seq
         (\di.
            list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e) (z:real^N))
              (dimindex (:N)))
         (dimindex (:N)))` in
  let premises_th =
    CONJ radii_th
      (CONJ radii_th
        (CONJ contains_th
          (CONJ outer_lengths_th row_lengths_th))) in
  let bound_th = MATCH_MP sound_th premises_th in
  let sum_imp =
    ISPECL
     [`boxes:(((num#num)#num)#((num#num)#num))list`;
      `\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e) (z:real^N)`]
     candle_q_weighted_rows_list_of_seq_sum in
  let boxes_length_th =
    ASSUME
     `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
      dimindex (:N)` in
  let sum_th = BETA_RULE (MATCH_MP sum_imp boxes_length_th) in
  ONCE_REWRITE_TAC[GSYM sum_th] THEN
  ACCEPT_TAC bound_th);;

let candle_q_dim_jet_m_taylor_error_sound = prove
 (`!e boxes box_jet.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_poly_jet_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     m_taylor_error
       (candle_poly_denote_dim e)
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_radius_vector boxes)
       (candle_q_real
         (candle_q_weighted_rows_abs_upper
           (candle_q_radius_list boxes)
           (candle_q_radius_list boxes)
           (candle_q_dim_jet_hessian box_jet)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  MATCH_MP_TAC candle_q_dim_jet_hessian_taylor_sum_bound THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let candle_q_dim_jet_taylor_upper_real = prove
 (`!boxes center_jet box_jet.
     candle_q_real
       (candle_q_dim_jet_taylor_upper boxes center_jet box_jet) =
     candle_q_real (SND (candle_q_dim_jet_f center_jet)) +
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_gradient center_jet)) +
     inv (&2) *
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_hessian box_jet))`,
  REWRITE_TAC[candle_q_dim_jet_taylor_upper_def;
              candle_q_dim_taylor_upper_def;
              candle_q_real_add; candle_q_real_mul;
              candle_q_real_half] THEN
  REAL_ARITH_TAC);;

let candle_q_dim_jet_taylor_upper_sound = prove
 (`!e boxes center_jet box_jet.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_poly_jet_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_poly_jet_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_poly_denote_dim e (p:real^N) <=
       candle_q_real
         (candle_q_dim_jet_taylor_upper boxes center_jet box_jet)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `m_cell_domain
     (candle_q_box_lower_vector boxes,
      candle_q_box_upper_vector boxes : real^N)
     (candle_q_box_center_vector boxes)
     (candle_q_box_radius_vector boxes)`
   (LABEL_TAC "cell_domain") THENL
   [ACCEPT_TAC
     (MATCH_MP candle_q_box_m_cell_domain
       (CONJ
         (ASSUME
           `LENGTH
             (boxes:(((num#num)#num)#((num#num)#num))list) =
            dimindex (:N)`)
         (ASSUME `candle_q_box_valid_list boxes`)));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diff2_domain
     (candle_q_box_lower_vector boxes,
      candle_q_box_upper_vector boxes : real^N)
     (candle_poly_denote_dim e)`
   (LABEL_TAC "diff2") THENL
   [REWRITE_TAC[diff2_domain] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ACCEPT_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (ISPECL [`e:candle_poly_expr`; `z:real^N`]
           candle_poly_denote_dim_diff2c)
         (ASSUME `candle_poly_valid_dim (dimindex (:N)) e`)));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_taylor_error
     (candle_poly_denote_dim e)
     (candle_q_box_lower_vector boxes,
      candle_q_box_upper_vector boxes : real^N)
     (candle_q_box_radius_vector boxes)
     (candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_hessian box_jet)))`
   (LABEL_TAC "taylor_error") THENL
   [ACCEPT_TAC
     (MATCH_MP candle_q_dim_jet_m_taylor_error_sound
       (CONJ
         (ASSUME `candle_poly_valid_dim (dimindex (:N)) e`)
         (CONJ
           (ASSUME
             `LENGTH
               (boxes:(((num#num)#num)#((num#num)#num))list) =
              dimindex (:N)`)
           (CONJ
             (ASSUME `candle_q_box_valid_list boxes`)
             (CONJ
               (ASSUME
                 `candle_q_dim_jet_shape (dimindex (:N)) box_jet`)
               (ASSUME
                 `!(z:real^N). z IN interval
                    [candle_q_box_lower_vector boxes,
                     candle_q_box_upper_vector boxes]
                    ==> candle_q_dim_poly_jet_contains (dimindex (:N))
                         box_jet
                         (list_of_seq (\k. z$(k + 1))
                           (dimindex (:N))) e`))))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_poly_denote_dim e
      (candle_q_box_center_vector boxes : real^N) <=
    candle_q_real (SND (candle_q_dim_jet_f center_jet))`
   (LABEL_TAC "center_bound") THENL
   [MP_TAC
     (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
       (ASSUME
         `candle_q_dim_poly_jet_contains (dimindex (:N)) center_jet
           (list_of_seq
             (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
             (dimindex (:N))) e`)) THEN
    ASM_SIMP_TAC[candle_poly_value_list_fun;
                 candle_poly_denote_dim_def;
                 candle_q_interval_contains_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (SND (candle_q_dim_jet_f center_jet)) +
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial i (candle_poly_denote_dim e)
               (candle_q_box_center_vector boxes : real^N))) +
    candle_q_real
      (candle_q_weighted_rows_abs_upper
        (candle_q_radius_list boxes)
        (candle_q_radius_list boxes)
        (candle_q_dim_jet_hessian box_jet)) / &2 <=
    candle_q_real
      (candle_q_dim_jet_taylor_upper boxes center_jet box_jet)`
   (LABEL_TAC "computed_upper_bound") THENL
   [SUBGOAL_THEN
     `sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs
              (partial i (candle_poly_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))) <=
      candle_q_real
        (candle_q_dot_abs_upper
          (candle_q_radius_list boxes)
          (candle_q_dim_jet_gradient center_jet))`
     (LABEL_TAC "gradient_bound") THENL
     [ACCEPT_TAC
       (MATCH_MP candle_q_dim_jet_gradient_taylor_sum_bound
         (CONJ
           (ASSUME `candle_poly_valid_dim (dimindex (:N)) e`)
           (CONJ
             (ASSUME
               `LENGTH
                 (boxes:(((num#num)#num)#((num#num)#num))list) =
                dimindex (:N)`)
             (CONJ
               (ASSUME `candle_q_box_valid_list boxes`)
               (CONJ
                 (ASSUME
                   `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)
                 (ASSUME
                   `candle_q_dim_poly_jet_contains (dimindex (:N))
                     center_jet
                     (list_of_seq
                       (\k. (candle_q_box_center_vector boxes : real^N)$
                         (k + 1))
                       (dimindex (:N))) e`))))));
      ALL_TAC] THEN
    ASM_REWRITE_TAC[candle_q_dim_jet_taylor_upper_real; real_div] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
   (ISPECL
     [`((candle_q_box_lower_vector boxes : real^N),
        (candle_q_box_upper_vector boxes : real^N))`;
      `(candle_q_box_center_vector boxes : real^N)`;
      `(candle_q_box_radius_vector boxes : real^N)`;
      `(candle_poly_denote_dim e : real^N->real)`;
      `candle_q_real
        (candle_q_weighted_rows_abs_upper
          (candle_q_radius_list boxes)
          (candle_q_radius_list boxes)
          (candle_q_dim_jet_hessian box_jet))`;
      `candle_q_real (SND (candle_q_dim_jet_f center_jet))`;
      `candle_q_real
        (candle_q_dim_jet_taylor_upper boxes center_jet box_jet)`]
     m_taylor_upper_bound) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `p:real^N`) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dim_poly_jet_normalized_center_shape = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_poly_jet_normalized
         (candle_q_center_environment_list boxes) e)`,
  REPEAT STRIP_TAC THEN
  let center_shape_th =
    ISPECL
     [`e:candle_poly_expr`;
      `candle_q_center_environment_list boxes`]
     candle_q_dim_poly_jet_normalized_shape in
  ACCEPT_TAC
   (REWRITE_RULE
     [candle_q_center_environment_list_length;
      ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`]
     center_shape_th));;

let candle_q_dim_poly_jet_normalized_center_sound = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_dim_poly_jet_contains (dimindex (:N))
       (candle_q_dim_poly_jet_normalized
         (candle_q_center_environment_list boxes) e)
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e`,
  REPEAT STRIP_TAC THEN
  let center_contains_th =
    MATCH_MP
     (SPEC
       `boxes:(((num#num)#num)#((num#num)#num))list`
       candle_q_center_environment_vector_contains)
     (ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`) in
  let center_jet_contains_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `candle_q_center_environment_list boxes`;
        `list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))`]
       candle_q_dim_poly_jet_normalized_sound)
     center_contains_th in
  ACCEPT_TAC
   (REWRITE_RULE
     [candle_q_center_environment_list_length;
      ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`]
     center_jet_contains_th));;

let candle_q_dim_poly_jet_normalized_box_shape = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REPEAT STRIP_TAC THEN
  let box_shape_th =
    ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`]
     candle_q_dim_poly_jet_normalized_shape in
  ACCEPT_TAC
   (REWRITE_RULE
     [ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`]
     box_shape_th));;

let candle_q_dim_poly_jet_normalized_box_sound = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     !(z:real^N). z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_q_dim_poly_jet_contains (dimindex (:N))
         (candle_q_dim_poly_jet_normalized boxes e)
         (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`,
  REPEAT STRIP_TAC THEN
  let box_contains_th =
    MATCH_MP
     (ISPECL
       [`boxes:(((num#num)#num)#((num#num)#num))list`;
        `z:real^N`]
       candle_q_box_stack_contains_vector)
     (CONJ
       (ASSUME
         `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
          dimindex (:N)`)
       (ASSUME
         `(z:real^N) IN interval
           [candle_q_box_lower_vector boxes,
            candle_q_box_upper_vector boxes]`)) in
  let box_jet_contains_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`;
        `list_of_seq (\k. (z:real^N)$(k + 1)) (dimindex (:N))`]
       candle_q_dim_poly_jet_normalized_sound)
     box_contains_th in
  ACCEPT_TAC
   (REWRITE_RULE
     [ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`]
     box_jet_contains_th));;

let candle_q_dim_poly_jet_whole_box_upper_sound = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_poly_denote_dim e (p:real^N) <=
       candle_q_real (candle_q_dim_poly_jet_whole_box_upper e boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_whole_box_upper_source] THEN
  MATCH_MP_TAC candle_q_dim_jet_taylor_upper_sound THEN
  ASM_REWRITE_TAC[] THEN
  let length_th =
    ASSUME
     `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
      dimindex (:N)` in
  let center_shape_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`]
       candle_q_dim_poly_jet_normalized_center_shape)
     length_th in
  let center_sound_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`]
       candle_q_dim_poly_jet_normalized_center_sound)
     length_th in
  let box_shape_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`]
       candle_q_dim_poly_jet_normalized_box_shape)
     length_th in
  let box_sound_th =
    MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`]
       candle_q_dim_poly_jet_normalized_box_sound)
     length_th in
  ACCEPT_TAC
   (CONJ center_shape_th
     (CONJ center_sound_th (CONJ box_shape_th box_sound_th))));;

let candle_q_dim_poly_jet_whole_box_accept_sound = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_poly_jet_whole_box_numerical_accept e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_poly_denote_dim e (p:real^N) < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_whole_box_numerical_accept_def] THEN
  STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
     (SPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`]
       candle_q_dim_poly_jet_whole_box_upper_sound)
     (CONJ
       (ASSUME `candle_poly_valid_dim (dimindex (:N)) e`)
       (CONJ
         (ASSUME
           `LENGTH
             (boxes:(((num#num)#num)#((num#num)#num))list) =
            dimindex (:N)`)
         (ASSUME `candle_q_box_valid_list boxes`))) in
  let upper_at_p =
    MATCH_MP (SPEC `p:real^N` upper_th)
     (ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`) in
  let upper_negative =
    REWRITE_RULE[candle_q_le_real; candle_q_dim_real_zero; REAL_NOT_LE]
     (ASSUME
       `~(candle_q_le candle_q_zero
           (candle_q_dim_poly_jet_whole_box_upper e boxes))`) in
  ACCEPT_TAC
   (MATCH_MP
     (ISPECL
       [`candle_poly_denote_dim e (p:real^N)`;
        `candle_q_real
          (candle_q_dim_poly_jet_whole_box_upper e boxes)`;
        `&0`]
       REAL_LET_TRANS)
     (CONJ upper_at_p upper_negative)));;

end;;
