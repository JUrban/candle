(* ========================================================================== *)
(* Whole-box Taylor soundness for reflected analytic shared jets.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Numerical value, gradient, and Hessian data    *)
(* stay inside one reflected jet.  The general Flyspeck Taylor theorem is     *)
(* instantiated only after the computed domain and component contracts have  *)
(* been proved.                                                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_flyspeck_bridge.ml";;

module Candle_cv_analytic_expr_taylor_sound = struct

open Multivariate_taylor;;
open Taylor_interval;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_flyspeck_bridge;;

(* This arithmetic lemma is source-language independent.  Keeping it here   *)
(* makes the reusable boundary explicit: a reflected jet need only supply    *)
(* interval containment for Flyspeck's ordered partial-derivative list.       *)

let candle_q_dim_jet_gradient_list_taylor_sum_bound = prove
 (`!f boxes center_jet.
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_stack_contains
       (candle_q_dim_jet_gradient center_jet)
       (list_of_seq
         (\di. partial (di + 1) (f:real^N->real)
           (candle_q_box_center_vector boxes : real^N))
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs
              (partial i f
                (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_gradient center_jet))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs (partial i f
             (candle_q_box_center_vector boxes : real^N))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs (partial ((i - 1) + 1) f
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
        (\di. partial (di + 1) f
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N)))`
   (LABEL_TAC "radius_gradient_lengths") THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let sound_th =
    SPECL
     [`candle_q_radius_list boxes`;
      `list_of_seq
        (\di. partial (di + 1) (f:real^N->real)
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
                (\di. partial (di + 1) (f:real^N->real)
                  (candle_q_box_center_vector boxes : real^N))
                (dimindex (:N)))`)
          (ASSUME
            `LENGTH (candle_q_radius_list boxes) =
             LENGTH
               (list_of_seq
                 (\di. partial (di + 1) (f:real^N->real)
                   (candle_q_box_center_vector boxes : real^N))
                 (dimindex (:N)))`))) in
  let sum_imp =
    ISPECL
     [`boxes:(((num#num)#num)#((num#num)#num))list`;
      `\di. partial (di + 1) (f:real^N->real)
        (candle_q_box_center_vector boxes : real^N)`]
     candle_q_dot_list_of_seq_sum in
  let sum_th =
    BETA_RULE
      (MATCH_MP sum_imp
        (ASSUME
          `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)) in
  let proposition_th =
    BETA_RULE
      (AP_TERM
        `\x:real.
           x <= candle_q_real
             (candle_q_dot_abs_upper
               (candle_q_radius_list boxes)
               (candle_q_dim_jet_gradient center_jet))`
        sum_th) in
  let result_th = EQ_MP proposition_th bound_th in
  ACCEPT_TAC result_th);;

let candle_q_box_center_stack_contains = prove
 (`!boxes.
     candle_q_box_valid_list boxes
     ==>
     candle_q_stack_contains boxes
       (MAP (\box. candle_q_real (candle_q_midpoint box)) boxes)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_q_box_valid_list_def;
              candle_q_stack_contains_def; MAP] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[candle_q_interval_contains_def] THEN
    MP_TAC
      (SPEC
        `h:((num#num)#num)#((num#num)#num)`
        candle_q_box_midpoint_radius) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_analytic_jet_gradient_taylor_sum_bound = prove
 (`!e boxes center_jet.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs
              (partial i (candle_analytic_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_gradient center_jet))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_jet_gradient_list_taylor_sum_bound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_dim_analytic_jet_gradient_flyspeck_contains THEN
  ASM_REWRITE_TAC[] THEN
  let center_map_contains_th =
    MATCH_MP
      (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
        candle_q_box_center_stack_contains)
      (ASSUME `candle_q_box_valid_list boxes`) in
  let center_list_th =
    MATCH_MP
      (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
        candle_q_box_center_vector_list)
      (ASSUME
        `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`) in
  let center_contains_th =
    REWRITE_RULE[GSYM center_list_th] center_map_contains_th in
  let regular_th =
    MATCH_MP
      (SPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))`]
        candle_q_dim_analytic_domain_regular)
      (CONJ center_contains_th
        (ASSUME `candle_q_dim_analytic_domain boxes e`)) in
  ACCEPT_TAC regular_th);;

let candle_q_dim_jet_hessian_list_taylor_sum_bound = prove
 (`!f boxes box_jet (z:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian box_jet)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
           (dimindex (:N)))
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                   abs (partial2 j i f z))) <=
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_hessian box_jet))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs
                    (partial2 j i (f:real^N->real) (z:real^N)))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs
                    (partial2 ((j - 1) + 1) ((i - 1) + 1)
                      (f:real^N->real) (z:real^N))))`
   (LABEL_TAC "hessian_indices") THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)`
   (LABEL_TAC "hessian_radii_nonnegative") THENL
   [MATCH_MP_TAC candle_q_radius_list_nonnegative THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_radius_list boxes) =
    LENGTH
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_outer_lengths") THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL
      (\values. LENGTH (candle_q_radius_list boxes) = LENGTH values)
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_row_lengths") THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC[candle_q_radius_list_length;
                 EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let values_tm =
    `list_of_seq
      (\di. list_of_seq
        (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) (z:real^N))
        (dimindex (:N)))
      (dimindex (:N))` in
  let sound_th =
    SPECL
      [`candle_q_radius_list boxes`;
       `candle_q_radius_list boxes`;
       values_tm;
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
          (\di. list_of_seq
            (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
            (dimindex (:N)))
          (dimindex (:N)))` in
  let outer_lengths_th =
    ASSUME
      `LENGTH (candle_q_radius_list boxes) =
       LENGTH
         (list_of_seq
           (\di. list_of_seq
             (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
             (dimindex (:N)))
           (dimindex (:N)))` in
  let row_lengths_th =
    ASSUME
      `ALL
        (\values. LENGTH (candle_q_radius_list boxes) = LENGTH values)
        (list_of_seq
          (\di. list_of_seq
            (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
            (dimindex (:N)))
          (dimindex (:N)))` in
  let bound_th =
    MATCH_MP sound_th
      (CONJ radii_th
        (CONJ radii_th
          (CONJ contains_th
            (CONJ outer_lengths_th row_lengths_th)))) in
  let sum_imp =
    ISPECL
      [`boxes:(((num#num)#num)#((num#num)#num))list`;
       `\di dj. partial2 (dj + 1) (di + 1)
         (f:real^N->real) (z:real^N)`]
      candle_q_weighted_rows_list_of_seq_sum in
  let sum_th =
    BETA_RULE
      (MATCH_MP sum_imp
        (ASSUME
          `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)) in
  let proposition_th =
    BETA_RULE
      (AP_TERM
        `\x:real.
           x <= candle_q_real
             (candle_q_weighted_rows_abs_upper
               (candle_q_radius_list boxes)
               (candle_q_radius_list boxes)
               (candle_q_dim_jet_hessian box_jet))`
        sum_th) in
  let indexed_result_th = EQ_MP proposition_th bound_th in
  USE_THEN "hessian_indices" (fun indices_th ->
    let index_proposition_th =
      BETA_RULE
        (AP_TERM
          `\x:real.
             x <= candle_q_real
               (candle_q_weighted_rows_abs_upper
                 (candle_q_radius_list boxes)
                 (candle_q_radius_list boxes)
                 (candle_q_dim_jet_hessian box_jet))`
          indices_th) in
    ACCEPT_TAC (EQ_MP (SYM index_proposition_th) indexed_result_th)));;

let candle_q_dim_analytic_jet_hessian_taylor_sum_bound = prove
 (`!e boxes box_jet (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes] /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) box_jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                   abs
                     (partial2 j i
                       (candle_analytic_denote_dim e) z))) <=
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_dim_jet_hessian box_jet))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_jet_hessian_list_taylor_sum_bound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_dim_analytic_jet_hessian_flyspeck_contains THEN
  ASM_REWRITE_TAC[] THEN
  let stack_th =
    MATCH_MP
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`; `z:real^N`]
        candle_q_box_stack_contains_vector)
      (CONJ
        (ASSUME
          `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)
        (ASSUME
          `(z:real^N) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) in
  ACCEPT_TAC
    (MATCH_MP
      (SPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `list_of_seq (\k. (z:real^N)$(k + 1)) (dimindex (:N))`]
        candle_q_dim_analytic_domain_regular)
      (CONJ stack_th
        (ASSUME `candle_q_dim_analytic_domain boxes e`))));;

let candle_q_dim_analytic_jet_m_taylor_error_sound = prove
 (`!e boxes box_jet.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     m_taylor_error
       (candle_analytic_denote_dim e)
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
  MATCH_MP_TAC candle_q_dim_analytic_jet_hessian_taylor_sum_bound THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let candle_q_dim_analytic_diff2_domain = prove
 (`!e boxes.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N)
     ==>
     diff2_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_analytic_denote_dim e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[diff2_domain] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC diff2c_imp_diff2 THEN
  MATCH_MP_TAC candle_analytic_denote_dim_diff2c THEN
  ASM_REWRITE_TAC[] THEN
  let stack_th =
    MATCH_MP
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`; `z:real^N`]
        candle_q_box_stack_contains_vector)
      (CONJ
        (ASSUME
          `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)
        (ASSUME
          `(z:real^N) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) in
  let regular_th =
    MATCH_MP
      (SPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `list_of_seq (\k. (z:real^N)$(k + 1)) (dimindex (:N))`]
        candle_q_dim_analytic_domain_regular)
      (CONJ stack_th
        (ASSUME `candle_q_dim_analytic_domain boxes e`)) in
  ACCEPT_TAC regular_th);;

let candle_q_dim_analytic_jet_taylor_upper_sound = prove
 (`!e boxes center_jet box_jet.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim e p <=
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
     (candle_analytic_denote_dim e)`
   (LABEL_TAC "diff2") THENL
   [MATCH_MP_TAC candle_q_dim_analytic_diff2_domain THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_taylor_error
     (candle_analytic_denote_dim e)
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
      (MATCH_MP candle_q_dim_analytic_jet_m_taylor_error_sound
        (CONJ
          (ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`)
          (CONJ
            (ASSUME `candle_q_dim_analytic_domain boxes e`)
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
                       ==> candle_q_dim_analytic_contains (dimindex (:N))
                            box_jet
                            (list_of_seq (\k. z$(k + 1))
                              (dimindex (:N))) e`)))))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_analytic_denote_dim e
      (candle_q_box_center_vector boxes : real^N) <=
    candle_q_real (SND (candle_q_dim_jet_f center_jet))`
   (LABEL_TAC "center_bound") THENL
   [MP_TAC
      (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                    candle_q_dim_jet_contains_components_def]
        (ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) e`)) THEN
    REWRITE_TAC[candle_analytic_denote_dim_def;
                candle_q_interval_contains_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (SND (candle_q_dim_jet_f center_jet)) +
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial i (candle_analytic_denote_dim e)
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
              (partial i (candle_analytic_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))) <=
      candle_q_real
        (candle_q_dot_abs_upper
          (candle_q_radius_list boxes)
          (candle_q_dim_jet_gradient center_jet))`
     (LABEL_TAC "gradient_bound") THENL
     [ACCEPT_TAC
        (MATCH_MP candle_q_dim_analytic_jet_gradient_taylor_sum_bound
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`)
            (CONJ
              (ASSUME `candle_q_dim_analytic_domain boxes e`)
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
                      `candle_q_dim_analytic_contains (dimindex (:N))
                        center_jet
                        (list_of_seq
                          (\k. (candle_q_box_center_vector boxes : real^N)$
                            (k + 1))
                          (dimindex (:N))) e`)))))));
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
      `(candle_analytic_denote_dim e : real^N->real)`;
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

end;;
