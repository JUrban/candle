(* ========================================================================== *)
(* Source invariant for the paired centered Taylor-model program.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Center and whole-box programs may use         *)
(* different square-root certificates.  When the accumulated domain bit is  *)
(* true, the rounded center jet denotes the center expression and the        *)
(* reconstructed proxy denotes the certificate-equivalent box expression.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_sound;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_invariant;;

(* The centered checker authenticates its own rounded proxy.  Its semantic
   contract must therefore state the regularity needed by Taylor's theorem,
   rather than require a second (and potentially looser) interval evaluator
   to accept the same source expression. *)

let candle_analytic_erase_regular_at = prove
 (`!e env.
     candle_analytic_regular_at env
       (candle_analytic_erase_sqrt_certificates e) <=>
     candle_analytic_regular_at env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def;
                  candle_analytic_regular_at_def;
                  candle_analytic_erase_value]);;

let candle_analytic_regular_certificate_transport = prove
 (`!center_e box_e env.
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e
     ==> (candle_analytic_regular_at env center_e <=>
          candle_analytic_regular_at env box_e)`,
  MESON_TAC[candle_analytic_erase_regular_at]);;

let candle_q_dim_analytic_regular_diff2_domain = prove
 (`!e boxes.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
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
  ASM_MESON_TAC[]);;

let candle_q_dim_analytic_jet_rounded_gradient_sum_bound_regular = prove
 (`!e boxes center_jet.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) center_jet
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e
     ==>
     sum (1..dimindex (:N))
       (\i.
          (candle_q_list_real_vector
            (candle_q_fixed_list_round_upper
              (candle_q_radius_list boxes)) : real^N)$i *
          abs
            (partial i (candle_analytic_denote_dim e)
              (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper_extended
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_dim_jet_gradient center_jet))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_jet_gradient_list_rounded_sum_bound THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_length;
                    candle_q_radius_list_length];
    MATCH_MP_TAC candle_q_fixed_list_round_upper_nonnegative THEN
    MATCH_MP_TAC candle_q_radius_list_nonnegative THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_analytic_jet_gradient_flyspeck_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_analytic_jet_complete_m_taylor_error_sound_regular = prove
 (`!e boxes box_jet.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
       (candle_q_list_real_vector
         (candle_q_fixed_list_round_upper
           (candle_q_radius_list boxes)))
       (candle_q_real
         (candle_q_weighted_rows_abs_upper_extended
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_fixed_interval_matrix_round
             (candle_q_dim_jet_hessian box_jet))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  SUBGOAL_THEN
   `ALL2 candle_q_stack_contains
      (candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet))
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1)
            (candle_analytic_denote_dim e) (z:real^N))
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "rounded_hessian_contains") THENL
   [MATCH_MP_TAC candle_q_fixed_interval_matrix_round_contains THEN
    MATCH_MP_TAC candle_q_dim_analytic_jet_hessian_flyspeck_contains THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (ISPECL
      [`candle_analytic_denote_dim e : real^N->real`;
       `candle_q_fixed_list_round_upper (candle_q_radius_list boxes)`;
       `candle_q_dim_jet_make candle_q_zero_interval []
          (candle_q_fixed_interval_matrix_round
            (candle_q_dim_jet_hessian box_jet))`;
       `z:real^N`]
      candle_q_dim_jet_hessian_list_rounded_sum_bound) THEN
  REWRITE_TAC[candle_q_dim_jet_make_def;
              candle_q_dim_jet_hessian_def; FST; SND] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_length;
                  candle_q_radius_list_length] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_fixed_list_round_upper_nonnegative THEN
    MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM candle_q_dim_jet_hessian_def] THEN
    MATCH_ACCEPT_TAC
      (ASSUME
        `ALL2 candle_q_stack_contains
          (candle_q_fixed_interval_matrix_round
            (candle_q_dim_jet_hessian box_jet))
          (list_of_seq
            (\di. list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_analytic_denote_dim e) (z:real^N))
              (dimindex (:N)))
            (dimindex (:N)))`)]);;

let candle_q_dim_analytic_jet_complete_partial_error_sound_regular = prove
 (`!e boxes box_jet i.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     i IN 1..dimindex (:N)
     ==>
     m_taylor_partial_error
       (candle_analytic_denote_dim e) i
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_list_real_vector
         (candle_q_fixed_list_round_upper
           (candle_q_radius_list boxes)))
       (candle_q_real
         (candle_q_dot_abs_upper_extended
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (EL (i - 1)
             (candle_q_fixed_interval_matrix_round
               (candle_q_dim_jet_hessian box_jet)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_partial_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_q_stack_contains
      (candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet))
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1)
            (candle_analytic_denote_dim e) (z:real^N))
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "rounded_hessian_contains") THENL
   [MATCH_MP_TAC candle_q_fixed_interval_matrix_round_contains THEN
    MATCH_MP_TAC candle_q_dim_analytic_jet_hessian_flyspeck_contains THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (EL (i - 1)
        (candle_q_fixed_interval_matrix_round
          (candle_q_dim_jet_hessian box_jet)))
      (list_of_seq
        (\dj. partial2 (dj + 1) i
          (candle_analytic_denote_dim e) (z:real^N))
        (dimindex (:N)))`
   (LABEL_TAC "rounded_row_contains") THENL
   [SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
     [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
      REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC
      (ISPECL
        [`candle_q_stack_contains`;
         `candle_q_fixed_interval_matrix_round
            (candle_q_dim_jet_hessian box_jet)`;
         `dimindex (:N)`;
         `\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim e) (z:real^N))
           (dimindex (:N))`;
         `i - 1`]
        candle_all2_right_list_of_seq_el) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM partial2] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\j.
         (candle_q_list_real_vector
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)) : real^N)$j *
         abs
           (partial2 j i (candle_analytic_denote_dim e) (z:real^N))) =
    sum (1..dimindex (:N))
      (\j.
         (candle_q_list_real_vector
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)) : real^N)$j *
         abs
           (partial2 ((j - 1) + 1) i
             (candle_analytic_denote_dim e) (z:real^N)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dot_abs_upper_extended_real] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) =
    LENGTH
      (list_of_seq
        (\dj. partial2 (dj + 1) i
          (candle_analytic_denote_dim e) (z:real^N))
        (dimindex (:N)))`
   (LABEL_TAC "partial_lengths") THENL
   [ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_length;
                    candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) =
    dimindex (:N)`
   (LABEL_TAC "partial_radii_length") THENL
   [ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_length;
                    candle_q_radius_list_length; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let radii_tm =
    `candle_q_fixed_list_round_upper (candle_q_radius_list boxes)` in
  let values_tm =
    `list_of_seq
      (\dj. partial2 (dj + 1) i
        (candle_analytic_denote_dim e) (z:real^N))
      (dimindex (:N))` in
  let intervals_tm =
    `EL (i - 1)
      (candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet))` in
  let nonnegative_th =
    MATCH_MP
      (SPEC `candle_q_radius_list boxes`
        candle_q_fixed_list_round_upper_nonnegative)
      (MATCH_MP
        (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
          candle_q_radius_list_nonnegative)
        (ASSUME `candle_q_box_valid_list boxes`)) in
  let lengths_th =
    ASSUME
     `LENGTH
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) =
      LENGTH
        (list_of_seq
          (\dj. partial2 (dj + 1) i
            (candle_analytic_denote_dim e) (z:real^N))
          (dimindex (:N)))` in
  let bound_th =
    MATCH_MP
      (SPECL [radii_tm; values_tm; intervals_tm]
        candle_q_dot_abs_upper_sound)
      (CONJ nonnegative_th
        (CONJ
          (ASSUME
            `candle_q_stack_contains
              (EL (i - 1)
                (candle_q_fixed_interval_matrix_round
                  (candle_q_dim_jet_hessian box_jet)))
              (list_of_seq
                (\dj. partial2 (dj + 1) i
                  (candle_analytic_denote_dim e) (z:real^N))
                (dimindex (:N)))`)
          lengths_th)) in
  let sum_th =
    BETA_RULE
      (MATCH_MP
        (ISPECL
          [radii_tm;
           `\dj. partial2 (dj + 1) i
             (candle_analytic_denote_dim e) (z:real^N)`]
          candle_q_dot_list_real_vector_sum)
        (ASSUME
          `LENGTH
             (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) =
           dimindex (:N)`)) in
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ITLIST2
      (\r y total. candle_q_real r * abs y + total)
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
      (list_of_seq
        (\dj. partial2 (dj + 1) i
          (candle_analytic_denote_dim e) (z:real^N))
        (dimindex (:N))) (&0)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[sum_th] THEN REWRITE_TAC[REAL_LE_REFL];
    ACCEPT_TAC bound_th]);;

let candle_q_dim_analytic_taylor_model_value_bound_contains_regular = prove
 (`!e boxes center_jet box_jet (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_interval_contains
       (candle_q_fixed_interval_round
         (candle_q_dim_taylor_model_value_bound
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_dim_first_jet_fixed_round center_jet)
           (candle_q_fixed_interval_matrix_round
             (candle_q_dim_jet_hessian box_jet))))
       (candle_analytic_denote_dim e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `radii =
      candle_q_fixed_list_round_upper (candle_q_radius_list boxes)` THEN
  ABBREV_TAC
   `rounded_center = candle_q_dim_first_jet_fixed_round center_jet` THEN
  ABBREV_TAC
   `rounded_hessian =
      candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet)` THEN
  ABBREV_TAC
   `error =
      candle_q_dim_taylor_model_error radii rounded_center rounded_hessian` THEN
  ABBREV_TAC
   `(value_bound:
       ((num#num)#num)#((num#num)#num)) =
      candle_q_dim_taylor_model_value_bound
        radii rounded_center rounded_hessian` THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape (dimindex (:N)) rounded_center`
   (LABEL_TAC "rounded_center_shape") THENL
   [EXPAND_TAC "rounded_center" THEN
    MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N)) rounded_center
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) e`
   (LABEL_TAC "rounded_center_contains") THENL
   [EXPAND_TAC "rounded_center" THEN
    MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_analytic_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_cell_domain
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_q_box_center_vector boxes)
      (candle_q_list_real_vector radii)`
   (LABEL_TAC "rounded_cell") THENL
   [EXPAND_TAC "radii" THEN
    MATCH_MP_TAC candle_q_fixed_list_round_upper_m_cell_domain THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diff2_domain
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_analytic_denote_dim e)`
   (LABEL_TAC "diff2") THENL
   [MATCH_MP_TAC candle_q_dim_analytic_regular_diff2_domain THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_taylor_error
      (candle_analytic_denote_dim e)
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_q_list_real_vector radii)
      (candle_q_real
        (candle_q_weighted_rows_abs_upper_extended
          radii radii rounded_hessian))`
   (LABEL_TAC "rounded_taylor_error") THENL
   [EXPAND_TAC "radii" THEN EXPAND_TAC "rounded_hessian" THEN
    MATCH_MP_TAC
      candle_q_dim_analytic_jet_complete_m_taylor_error_sound_regular THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval_arith
      (candle_analytic_denote_dim e
        (candle_q_box_center_vector boxes : real^N))
      (candle_q_real (FST (candle_q_dim_jet_f rounded_center)),
       candle_q_real (SND (candle_q_dim_jet_f rounded_center)))`
   (LABEL_TAC "center_interval") THENL
   [MP_TAC
      (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                    candle_q_dim_jet_contains_components_def]
        (ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) rounded_center
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) e`)) THEN
    REWRITE_TAC[candle_analytic_denote_dim_def;
                candle_q_interval_contains_def;
                Interval_arith.interval_arith] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs
             (partial i (candle_analytic_denote_dim e)
               (candle_q_box_center_vector boxes : real^N))) +
    candle_q_real
      (candle_q_weighted_rows_abs_upper_extended
        radii radii rounded_hessian) / &2 <=
    candle_q_real error`
   (LABEL_TAC "computed_error_bound") THENL
   [SUBGOAL_THEN
     `sum (1..dimindex (:N))
        (\i. (candle_q_list_real_vector radii : real^N)$i *
             abs
               (partial i (candle_analytic_denote_dim e)
                 (candle_q_box_center_vector boxes : real^N))) <=
      candle_q_real
        (candle_q_dot_abs_upper_extended radii
          (candle_q_dim_jet_gradient rounded_center))`
     ASSUME_TAC THENL
     [EXPAND_TAC "radii" THEN
      MATCH_MP_TAC
        candle_q_dim_analytic_jet_rounded_gradient_sum_bound_regular THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "error" THEN
    REWRITE_TAC[candle_q_dim_taylor_model_error_real; real_div] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  let bounds_th =
      ISPECL
        [`((candle_q_box_lower_vector boxes : real^N),
           (candle_q_box_upper_vector boxes : real^N))`;
         `(candle_q_box_center_vector boxes : real^N)`;
         `(candle_q_list_real_vector radii : real^N)`;
         `(candle_analytic_denote_dim e : real^N->real)`;
         `candle_q_real
           (candle_q_weighted_rows_abs_upper_extended
             radii radii rounded_hessian)`;
         `candle_q_real (FST (candle_q_dim_jet_f rounded_center))`;
         `candle_q_real (SND (candle_q_dim_jet_f rounded_center))`;
         `candle_q_real error`;
         `candle_q_real
            (FST (value_bound:((num#num)#num)#((num#num)#num)))`;
         `candle_q_real
            (SND (value_bound:((num#num)#num)#((num#num)#num)))`]
        m_taylor_bounds in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_cell_domain
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_q_box_center_vector boxes)
            (candle_q_list_real_vector radii)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `diff2_domain
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_analytic_denote_dim e)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_taylor_error
            (candle_analytic_denote_dim e)
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_q_list_real_vector radii)
            (candle_q_real
              (candle_q_weighted_rows_abs_upper_extended
                radii radii rounded_hessian))`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `interval_arith
            (candle_analytic_denote_dim e
              (candle_q_box_center_vector boxes : real^N))
            (candle_q_real (FST (candle_q_dim_jet_f rounded_center)),
             candle_q_real (SND (candle_q_dim_jet_f rounded_center)))`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `sum (1..dimindex (:N))
             (\i. (candle_q_list_real_vector radii : real^N)$i *
                  abs
                    (partial i (candle_analytic_denote_dim e)
                      (candle_q_box_center_vector boxes : real^N))) +
           candle_q_real
             (candle_q_weighted_rows_abs_upper_extended
               radii radii rounded_hessian) / &2 <=
           candle_q_real error`) in
  let value_real_th =
      SPECL
        [`radii:((num#num)#num)list`;
         `rounded_center:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `rounded_hessian:
            ((((num#num)#num)#((num#num)#num))list)list`]
        candle_q_dim_taylor_model_value_bound_real in
  let value_real_th =
      REWRITE_RULE
        [ASSUME
          `candle_q_dim_taylor_model_value_bound
             radii rounded_center rounded_hessian =
           (value_bound:((num#num)#num)#((num#num)#num))`;
         ASSUME
          `candle_q_dim_taylor_model_error
             radii rounded_center rounded_hessian = error`]
        value_real_th in
  let lower_eq = CONJUNCT1 value_real_th in
  let upper_eq = SYM (CONJUNCT2 value_real_th) in
  let lower_th =
      MATCH_MP
        (SPECL [lhand (concl lower_eq); rand (concl lower_eq)]
          REAL_EQ_IMP_LE)
        lower_eq in
  let upper_th =
      MATCH_MP
        (SPECL [lhand (concl upper_eq); rand (concl upper_eq)]
          REAL_EQ_IMP_LE)
        upper_eq in
  let bounded_th = MATCH_MP (MATCH_MP bounds_th lower_th) upper_th in
  MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC
    (REWRITE_RULE[m_bounded_on_int] bounded_th) THEN
  DISCH_THEN (MP_TAC o SPEC `p:real^N`) THEN
  ASM_REWRITE_TAC[Interval_arith.interval_arith] THEN
  EXPAND_TAC "value_bound" THEN EXPAND_TAC "rounded_hessian" THEN
  EXPAND_TAC "rounded_center" THEN EXPAND_TAC "radii");;

let candle_q_dim_analytic_taylor_model_gradient_component_contains_regular = prove
 (`!e boxes center_jet box_jet (p:real^N) i.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     i IN 1..dimindex (:N) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_interval_contains
       (candle_q_fixed_interval_round
         (EL (i - 1)
           (candle_q_dim_taylor_model_gradient_bounds
             (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
             (candle_q_dim_jet_gradient
               (candle_q_dim_first_jet_fixed_round center_jet))
             (candle_q_fixed_interval_matrix_round
               (candle_q_dim_jet_hessian box_jet)))))
       (partial i (candle_analytic_denote_dim e) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `radii =
      candle_q_fixed_list_round_upper (candle_q_radius_list boxes)` THEN
  ABBREV_TAC
   `rounded_center = candle_q_dim_first_jet_fixed_round center_jet` THEN
  ABBREV_TAC
   `rounded_hessian =
      candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet)` THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape (dimindex (:N)) rounded_center`
   (LABEL_TAC "rounded_center_shape") THENL
   [EXPAND_TAC "rounded_center" THEN
    MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N)) rounded_center
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) e`
   (LABEL_TAC "rounded_center_contains") THENL
   [EXPAND_TAC "rounded_center" THEN
    MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_analytic_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let center_regular_th =
    ASSUME
      `candle_analytic_regular_at
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) e` in
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_dim_jet_gradient rounded_center)
      (list_of_seq
        (\di. partial (di + 1) (candle_analytic_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N)))`
   (LABEL_TAC "center_gradient_contains") THENL
   [MATCH_MP_TAC candle_q_dim_analytic_jet_gradient_flyspeck_contains THEN
    ASM_REWRITE_TAC[center_regular_th];
    ALL_TAC] THEN
  let gradient_length_th =
    CONJUNCT1
      (REWRITE_RULE[candle_q_dim_jet_shape_def]
        (ASSUME
          `candle_q_dim_jet_shape (dimindex (:N)) rounded_center`)) in
  let interval_lookup_th =
    MATCH_MP
      (SPECL
        [`candle_q_dim_jet_gradient rounded_center`; `i - 1`]
        candle_q_interval_lookup_in_range)
      (REWRITE_RULE[GSYM gradient_length_th]
        (ASSUME `i - 1 < dimindex (:N)`)) in
  let real_lookup_th =
    MATCH_MP
      (ISPECL
        [`\di. partial (di + 1) (candle_analytic_denote_dim e)
           (candle_q_box_center_vector boxes : real^N)`;
         `dimindex (:N)`; `i - 1`]
        candle_q_real_lookup_list_of_seq)
      (ASSUME `i - 1 < dimindex (:N)`) in
  let real_lookup_th =
    REWRITE_RULE[ASSUME `(i - 1) + 1 = i`] real_lookup_th in
  let lookup_th =
    MATCH_MP
      (SPECL
        [`i - 1`;
         `candle_q_dim_jet_gradient rounded_center`;
         `list_of_seq
            (\di. partial (di + 1) (candle_analytic_denote_dim e)
              (candle_q_box_center_vector boxes : real^N))
            (dimindex (:N))`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains
          (candle_q_dim_jet_gradient rounded_center)
          (list_of_seq
            (\di. partial (di + 1) (candle_analytic_denote_dim e)
              (candle_q_box_center_vector boxes : real^N))
            (dimindex (:N)))`) in
  let center_partial_th =
    REWRITE_RULE[interval_lookup_th; real_lookup_th] lookup_th in
  ASSUME_TAC center_partial_th THEN
  ABBREV_TAC
   `(center_interval:
       ((num#num)#num)#((num#num)#num)) =
      EL (i - 1) (candle_q_dim_jet_gradient rounded_center)` THEN
  ABBREV_TAC
   `(partial_error_q:(num#num)#num) =
      candle_q_dot_abs_upper_extended radii
        (EL (i - 1) rounded_hessian)` THEN
  ABBREV_TAC
   `(gradient_bound:
       ((num#num)#num)#((num#num)#num)) =
      candle_q_interval_add_extended center_interval
        (candle_q_symmetric_interval partial_error_q)` THEN
  let box_shape_th =
    REWRITE_RULE[candle_q_dim_jet_shape_def;
                 candle_q_dim_interval_matrix_shape_def]
      (ASSUME
        `candle_q_dim_jet_shape (dimindex (:N)) box_jet`) in
  let box_hessian_length_th =
    CONJUNCT1 (CONJUNCT2 box_shape_th) in
  let rounded_hessian_length_th =
    REWRITE_RULE
      [ASSUME
        `candle_q_fixed_interval_matrix_round
           (candle_q_dim_jet_hessian box_jet) = rounded_hessian`]
      (TRANS
        (SPEC `candle_q_dim_jet_hessian box_jet`
          candle_q_fixed_interval_matrix_round_length)
        box_hessian_length_th) in
  let gradient_hessian_lengths_th =
    TRANS gradient_length_th (SYM rounded_hessian_length_th) in
  ASSUME_TAC gradient_hessian_lengths_th THEN
  let gradient_index_th =
    REWRITE_RULE[GSYM gradient_length_th]
      (ASSUME `i - 1 < dimindex (:N)`) in
  let gradient_bound_el_th =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `candle_q_dim_jet_gradient rounded_center`;
         `rounded_hessian:
            ((((num#num)#num)#((num#num)#num))list)list`;
         `i - 1`]
        candle_q_dim_taylor_model_gradient_bounds_el)
      (CONJ gradient_hessian_lengths_th gradient_index_th) in
  let gradient_bound_el_th =
    REWRITE_RULE
      [ASSUME
        `EL (i - 1) (candle_q_dim_jet_gradient rounded_center) =
         center_interval`;
       ASSUME
        `candle_q_dot_abs_upper_extended radii
           (EL (i - 1) rounded_hessian) = partial_error_q`;
       ASSUME
        `candle_q_interval_add_extended center_interval
           (candle_q_symmetric_interval partial_error_q) =
         gradient_bound`]
      gradient_bound_el_th in
  ASSUME_TAC gradient_bound_el_th THEN
  SUBGOAL_THEN
   `m_cell_domain
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_q_box_center_vector boxes)
      (candle_q_list_real_vector radii)`
   (LABEL_TAC "rounded_cell") THENL
   [EXPAND_TAC "radii" THEN
    MATCH_MP_TAC candle_q_fixed_list_round_upper_m_cell_domain THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diff2_domain
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_analytic_denote_dim e)`
   (LABEL_TAC "diff2") THENL
   [MATCH_MP_TAC candle_q_dim_analytic_regular_diff2_domain THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_taylor_partial_error
      (candle_analytic_denote_dim e) i
      (candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes : real^N)
      (candle_q_list_real_vector radii)
      (candle_q_real partial_error_q)`
   (LABEL_TAC "partial_error") THENL
   [EXPAND_TAC "partial_error_q" THEN EXPAND_TAC "rounded_hessian" THEN
    EXPAND_TAC "radii" THEN
    MATCH_MP_TAC candle_q_dim_analytic_jet_complete_partial_error_sound_regular THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval_arith
      (partial i (candle_analytic_denote_dim e)
        (candle_q_box_center_vector boxes : real^N))
      (candle_q_real (FST center_interval),
       candle_q_real (SND center_interval))`
   (LABEL_TAC "center_partial_interval") THENL
   [EXPAND_TAC "center_interval" THEN
    MP_TAC
      (ASSUME
        `candle_q_interval_contains
          (EL (i - 1) (candle_q_dim_jet_gradient rounded_center))
          (partial i (candle_analytic_denote_dim e)
            (candle_q_box_center_vector boxes : real^N))`) THEN
    REWRITE_TAC[candle_q_interval_contains_def;
                Interval_arith.interval_arith];
    ALL_TAC] THEN
  let bounds_th =
      ISPECL
        [`((candle_q_box_lower_vector boxes : real^N),
           (candle_q_box_upper_vector boxes : real^N))`;
         `(candle_q_box_center_vector boxes : real^N)`;
         `(candle_q_list_real_vector radii : real^N)`;
         `(candle_analytic_denote_dim e : real^N->real)`;
         `i:num`;
         `candle_q_real partial_error_q`;
         `candle_q_real (FST center_interval)`;
         `candle_q_real (SND center_interval)`;
         `candle_q_real (FST gradient_bound)`;
         `candle_q_real (SND gradient_bound)`]
        m_taylor_partial_bounds in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_cell_domain
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_q_box_center_vector boxes)
            (candle_q_list_real_vector radii)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `diff2_domain
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_analytic_denote_dim e)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_taylor_partial_error
            (candle_analytic_denote_dim e) i
            (candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes : real^N)
            (candle_q_list_real_vector radii)
            (candle_q_real partial_error_q)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `interval_arith
            (partial i (candle_analytic_denote_dim e)
              (candle_q_box_center_vector boxes : real^N))
            (candle_q_real (FST center_interval),
             candle_q_real (SND center_interval))`) in
  let bound_real_th =
      REWRITE_RULE
        [ASSUME
          `candle_q_interval_add_extended center_interval
             (candle_q_symmetric_interval partial_error_q) =
           gradient_bound`]
        (ISPECL
          [`center_interval:
             ((num#num)#num)#((num#num)#num)`;
           `partial_error_q:(num#num)#num`]
          candle_q_interval_add_symmetric_real) in
  let lower_eq = CONJUNCT1 bound_real_th in
  let upper_eq = SYM (CONJUNCT2 bound_real_th) in
  let lower_th =
      MATCH_MP
        (SPECL [lhand (concl lower_eq); rand (concl lower_eq)]
          REAL_EQ_IMP_LE)
        lower_eq in
  let upper_th =
      MATCH_MP
        (SPECL [lhand (concl upper_eq); rand (concl upper_eq)]
          REAL_EQ_IMP_LE)
        upper_eq in
  let bounded_th = MATCH_MP (MATCH_MP bounds_th lower_th) upper_th in
  ONCE_REWRITE_TAC
    [ASSUME
      `EL (i - 1)
         (candle_q_dim_taylor_model_gradient_bounds radii
           (candle_q_dim_jet_gradient rounded_center) rounded_hessian) =
       gradient_bound`] THEN
  MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC (REWRITE_RULE[m_bounded_on_int] bounded_th) THEN
  DISCH_THEN (MP_TAC o SPEC `p:real^N`) THEN
  ASM_REWRITE_TAC[Interval_arith.interval_arith] THEN
  EXPAND_TAC "gradient_bound" THEN EXPAND_TAC "partial_error_q" THEN
  EXPAND_TAC "center_interval" THEN EXPAND_TAC "rounded_hessian" THEN
  EXPAND_TAC "rounded_center" THEN EXPAND_TAC "radii");;


let candle_q_dim_analytic_taylor_model_gradient_contains_regular = prove
 (`!e boxes center_jet box_jet (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_stack_contains
       (candle_q_fixed_interval_list_round
         (candle_q_dim_taylor_model_gradient_bounds
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_dim_jet_gradient
             (candle_q_dim_first_jet_fixed_round center_jet))
           (candle_q_fixed_interval_matrix_round
             (candle_q_dim_jet_hessian box_jet))))
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) p)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `(gradient_bounds:
       (((num#num)#num)#((num#num)#num))list) =
      candle_q_fixed_interval_list_round
        (candle_q_dim_taylor_model_gradient_bounds
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_q_dim_jet_gradient
            (candle_q_dim_first_jet_fixed_round center_jet))
          (candle_q_fixed_interval_matrix_round
            (candle_q_dim_jet_hessian box_jet)))` THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_first_jet_fixed_round center_jet)`
   (LABEL_TAC "rounded_center_shape") THENL
   [MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (gradient_bounds:
        (((num#num)#num)#((num#num)#num))list) = dimindex (:N)`
   ASSUME_TAC THENL
   [EXPAND_TAC "gradient_bounds" THEN
    REWRITE_TAC[candle_q_fixed_interval_list_round_length] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `LENGTH
        (candle_q_dim_jet_gradient
          (candle_q_dim_first_jet_fixed_round center_jet))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_taylor_model_gradient_bounds_length THEN
      REWRITE_TAC[candle_q_fixed_interval_matrix_round_length] THEN
      MP_TAC
        (REWRITE_RULE[candle_q_dim_jet_shape_def;
                      candle_q_dim_interval_matrix_shape_def]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N)) box_jet`)) THEN
      MP_TAC
        (REWRITE_RULE[candle_q_dim_jet_shape_def]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N))
              (candle_q_dim_first_jet_fixed_round center_jet)`)) THEN
      MESON_TAC[];
      MP_TAC
        (REWRITE_RULE[candle_q_dim_jet_shape_def]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N))
              (candle_q_dim_first_jet_fixed_round center_jet)`)) THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(gradient_bounds:
       (((num#num)#num)#((num#num)#num))list) =
    list_of_seq
      (\di. EL di
        (gradient_bounds:
          (((num#num)#num)#((num#num)#num))list))
      (dimindex (:N))`
   (LABEL_TAC "gradient_sequence") THENL
   [ACCEPT_TAC
      (MATCH_MP
        (ISPECL
          [`dimindex (:N)`;
           `gradient_bounds:
              (((num#num)#num)#((num#num)#num))list`]
          candle_list_eq_list_of_seq_el)
        (ASSUME
          `LENGTH
             (gradient_bounds:
               (((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`));
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  ONCE_REWRITE_TAC
    [ASSUME
      `(gradient_bounds:
          (((num#num)#num)#((num#num)#num))list) =
       list_of_seq
         (\di. EL di
           (gradient_bounds:
             (((num#num)#num)#((num#num)#num))list))
         (dimindex (:N))`] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `di + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_dim_taylor_model_gradient_bounds
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_dim_jet_gradient
          (candle_q_dim_first_jet_fixed_round center_jet))
        (candle_q_fixed_interval_matrix_round
          (candle_q_dim_jet_hessian box_jet))) = dimindex (:N)`
   (LABEL_TAC "unrounded_gradient_length") THENL
   [UNDISCH_TAC
      `LENGTH
         (gradient_bounds:
           (((num#num)#num)#((num#num)#num))list) = dimindex (:N)` THEN
    EXPAND_TAC "gradient_bounds" THEN
    REWRITE_TAC[candle_q_fixed_interval_list_round_length];
    ALL_TAC] THEN
  EXPAND_TAC "gradient_bounds" THEN
  ASM_SIMP_TAC[candle_q_fixed_interval_list_round_el] THEN
  let component_th =
    ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `box_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `p:real^N`;
         `di + 1`]
        candle_q_dim_analytic_taylor_model_gradient_component_contains_regular in
  let component_premises =
    end_itlist CONJ
        [ASSUME
          `candle_analytic_valid_dim (dimindex (:N)) e`;
         ASSUME
          `candle_analytic_regular_at
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) e`;
         ASSUME
          `!(z:real^N). z IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]
            ==> candle_analytic_regular_at
                  (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
         ASSUME
          `LENGTH
             (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`;
         ASSUME `candle_q_box_valid_list boxes`;
         ASSUME
          `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
         ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k.
                (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) e`;
         ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
         ASSUME
          `!(z:real^N). z IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]
            ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                  (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
         ASSUME `di + 1 IN 1..dimindex (:N)`;
         ASSUME
          `(p:real^N) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`] in
  ACCEPT_TAC
    (REWRITE_RULE[ARITH_RULE `(di + 1) - 1 = di`]
      (MATCH_MP component_th component_premises)));;


let candle_q_dim_analytic_taylor_model_gradient_analytic_contains_regular = prove
 (`!e boxes center_jet box_jet (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_stack_contains
       (candle_q_fixed_interval_list_round
         (candle_q_dim_taylor_model_gradient_bounds
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_dim_jet_gradient
             (candle_q_dim_first_jet_fixed_round center_jet))
           (candle_q_fixed_interval_matrix_round
             (candle_q_dim_jet_hessian box_jet))))
       (list_of_seq
         (\di. candle_analytic_d di
           (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let partial_gradient_th =
    ISPECL
      [`e:candle_analytic_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `box_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `p:real^N`]
      candle_q_dim_analytic_taylor_model_gradient_contains_regular in
  let partial_gradient_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME
        `candle_analytic_regular_at
          (list_of_seq
            (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
            (dimindex (:N))) e`;
       ASSUME
        `!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_analytic_regular_at
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
       ASSUME
        `LENGTH
           (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`;
       ASSUME `candle_q_box_valid_list boxes`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
       ASSUME
        `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
          (list_of_seq
            (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
            (dimindex (:N))) e`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
       ASSUME
        `!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
       ASSUME
        `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`] in
  let partial_gradient_th =
    MATCH_MP partial_gradient_th partial_gradient_premises in
  ASSUME_TAC partial_gradient_th THEN
  let regular_th =
    MATCH_MP
      (SPEC `p:real^N`
        (ASSUME
          `!(z:real^N). z IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]
            ==> candle_analytic_regular_at
                  (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`))
      (ASSUME
        `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`) in
  ASSUME_TAC regular_th THEN
  SUBGOAL_THEN
   `list_of_seq
      (\di. partial (di + 1) (candle_analytic_denote_dim e) (p:real^N))
      (dimindex (:N)) =
    list_of_seq
      (\di. candle_analytic_d di
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) e)
      (dimindex (:N))`
   (LABEL_TAC "gradient_semantic_list") THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `di:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    MP_TAC
      (SPECL
        [`e:candle_analytic_expr`; `p:real^N`; `di + 1`]
        candle_analytic_denote_dim_partial) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th])] THEN
    REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC
    [GSYM
      (ASSUME
        `list_of_seq
           (\di. partial (di + 1) (candle_analytic_denote_dim e)
             (p:real^N))
           (dimindex (:N)) =
         list_of_seq
           (\di. candle_analytic_d di
             (list_of_seq (\k. (p:real^N)$(k + 1))
               (dimindex (:N))) e)
           (dimindex (:N))`)] THEN
  ASM_REWRITE_TAC[]);;


let candle_q_dim_analytic_taylor_model_proxy_contains_regular = prove
 (`!e boxes center_jet box_jet (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
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
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_q_dim_taylor_model_result_complete
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           T center_jet (candle_q_dim_jet_hessian box_jet)))
       (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM candle_q_dim_analytic_taylor_model_box_proxy_def] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_analytic_taylor_model_box_proxy
        boxes center_jet box_jet)`
   (LABEL_TAC "proxy_shape") THENL
   [REWRITE_TAC[candle_q_dim_analytic_taylor_model_box_proxy_def] THEN
    ASM_MESON_TAC[candle_q_dim_taylor_model_result_complete_proxy_shape];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_dim_jet_f
        (candle_q_dim_analytic_taylor_model_box_proxy
          boxes center_jet box_jet))
      (candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) e)`
   (LABEL_TAC "proxy_value") THENL
   [REWRITE_TAC[candle_q_dim_analytic_taylor_model_box_proxy_def] THEN
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_q_dim_taylor_model_result_complete_def;
                candle_q_dim_taylor_model_result_complete_rounded_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_value_bound_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                FST; SND] THEN
    REWRITE_TAC[GSYM candle_analytic_denote_dim_def] THEN
    ASM_MESON_TAC[candle_q_dim_analytic_taylor_model_value_bound_contains_regular];
    ALL_TAC] THEN
  let gradient_th =
    ISPECL
      [`e:candle_analytic_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `box_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `p:real^N`]
      candle_q_dim_analytic_taylor_model_gradient_analytic_contains_regular in
  let gradient_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME
        `candle_analytic_regular_at
          (list_of_seq
            (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
            (dimindex (:N))) e`;
       ASSUME
        `!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_analytic_regular_at
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
       ASSUME
        `LENGTH
           (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`;
       ASSUME `candle_q_box_valid_list boxes`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
       ASSUME
        `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
          (list_of_seq
            (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
            (dimindex (:N))) e`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
       ASSUME
        `!(z:real^N). z IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
       ASSUME
        `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`] in
  let gradient_contains_th = MATCH_MP gradient_th gradient_premises in
  ASSUME_TAC gradient_contains_th THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_dim_jet_gradient
        (candle_q_dim_analytic_taylor_model_box_proxy
          boxes center_jet box_jet))
      (list_of_seq
        (\di. candle_analytic_d di
          (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) e)
        (dimindex (:N)))`
   (LABEL_TAC "proxy_gradient") THENL
   [REWRITE_TAC[candle_q_dim_analytic_taylor_model_box_proxy_def] THEN
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_q_dim_taylor_model_result_complete_def;
                candle_q_dim_taylor_model_result_complete_rounded_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_gradient_bounds_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
                FST; SND] THEN
    ACCEPT_TAC
      (REWRITE_RULE[candle_q_dim_jet_gradient_def] gradient_contains_th);
    ALL_TAC] THEN
  let box_contains_at_p =
    MATCH_MP
      (SPEC `p:real^N`
        (ASSUME
          `!(z:real^N). z IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]
            ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                  (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`))
      (ASSUME
        `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`) in
  let box_components_at_p =
    REWRITE_RULE[candle_q_dim_analytic_contains_def] box_contains_at_p in
  let proxy_hessian_th =
    MATCH_MP
      (ISPECL
        [`dimindex (:N)`;
         `candle_q_fixed_list_round_upper (candle_q_radius_list boxes)`;
         `T`;
         `center_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `box_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `candle_analytic_value
            (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) e`;
         `(\di. candle_analytic_d di
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e):num->real`;
         `(\di dj. candle_analytic_dd di dj
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e):num->num->real`]
        candle_q_dim_taylor_model_result_complete_proxy_hessian_contains)
      (CONJ
        (ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`)
        box_components_at_p) in
  ASSUME_TAC proxy_hessian_th THEN
  SUBGOAL_THEN
   `ALL2 candle_q_stack_contains
      (candle_q_dim_jet_hessian
        (candle_q_dim_analytic_taylor_model_box_proxy
          boxes center_jet box_jet))
      (list_of_seq
        (\di. list_of_seq
          (\dj. candle_analytic_dd di dj
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e)
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "proxy_hessian") THENL
   [REWRITE_TAC[candle_q_dim_analytic_taylor_model_box_proxy_def] THEN
    ACCEPT_TAC (BETA_RULE proxy_hessian_th);
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
  let components_th =
    MATCH_MP
      (BETA_RULE (ISPECL
        [`dimindex (:N)`;
         `candle_q_dim_analytic_taylor_model_box_proxy
            boxes center_jet box_jet`;
         `candle_analytic_value
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e`;
         `(\di. candle_analytic_d di
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e):num->real`;
         `(\di dj. candle_analytic_dd di dj
            (list_of_seq (\k. (p:real^N)$(k + 1))
              (dimindex (:N))) e):num->num->real`]
        candle_q_dim_jet_contains_components_of_stacks))
      (BETA_RULE (end_itlist CONJ
        [ASSUME
          `candle_q_dim_jet_shape (dimindex (:N))
            (candle_q_dim_analytic_taylor_model_box_proxy
              boxes center_jet box_jet)`;
         ASSUME
          `candle_q_interval_contains
            (candle_q_dim_jet_f
              (candle_q_dim_analytic_taylor_model_box_proxy
                boxes center_jet box_jet))
            (candle_analytic_value
              (list_of_seq (\k. (p:real^N)$(k + 1))
                (dimindex (:N))) e)`;
         ASSUME
          `candle_q_stack_contains
            (candle_q_dim_jet_gradient
              (candle_q_dim_analytic_taylor_model_box_proxy
                boxes center_jet box_jet))
            (list_of_seq
              (\di. candle_analytic_d di
                (list_of_seq (\k. (p:real^N)$(k + 1))
                  (dimindex (:N))) e)
              (dimindex (:N)))`;
         ASSUME
          `ALL2 candle_q_stack_contains
            (candle_q_dim_jet_hessian
              (candle_q_dim_analytic_taylor_model_box_proxy
                boxes center_jet box_jet))
            (list_of_seq
              (\di. list_of_seq
                (\dj. candle_analytic_dd di dj
                  (list_of_seq (\k. (p:real^N)$(k + 1))
                    (dimindex (:N))) e)
                (dimindex (:N)))
              (dimindex (:N)))`])) in
  MATCH_ACCEPT_TAC components_th);;


let candle_q_dim_taylor_model_result_analytic_invariant_def =
  new_definition
 `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N)
      (boxes:(((num#num)#num)#((num#num)#num))list)
      result center_e box_e <=>
    candle_q_dim_taylor_model_result_domain result
    ==>
    candle_analytic_regular_at
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) center_e /\
    (!(p:real^N). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e) /\
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_result_center result) /\
    candle_q_dim_analytic_contains (dimindex (:N))
      (candle_q_dim_taylor_model_result_center result)
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) center_e /\
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_proxy result) /\
    (!(p:real^N). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_q_dim_analytic_contains (dimindex (:N))
              (candle_q_dim_taylor_model_proxy result)
              (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e)`;;

let candle_q_dim_taylor_model_result_complete_domain = prove
 (`!radii domain center_jet box_jet.
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_result_complete radii domain center_jet
         (candle_q_dim_jet_hessian box_jet)) = domain`,
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_q_dim_taylor_model_complete_analytic_invariant = prove
 (`!center_e box_e boxes domain center_jet box_jet (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     (domain ==>
       candle_analytic_regular_at
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       (!(p:real^N). p IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_analytic_regular_at
                (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e) /\
       candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
       candle_q_dim_analytic_contains (dimindex (:N)) center_jet
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
       (!(p:real^N). p IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       (candle_q_dim_taylor_model_result_complete
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         domain center_jet (candle_q_dim_jet_hessian box_jet))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "complete_premises") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_q_dim_taylor_model_result_complete_domain] THEN
  DISCH_TAC THEN
  USE_THEN "complete_premises"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_center_shape THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_center_contains THEN
    ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_proxy_shape THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    let center_contains_box_e =
      EQ_MP
        (MATCH_MP
          (ISPECL
            [`dimindex (:N)`; `center_jet:
               (((num#num)#num)#((num#num)#num))#
               ((((num#num)#num)#((num#num)#num))list#
                (((((num#num)#num)#((num#num)#num))list)list))`;
             `list_of_seq
               (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
               (dimindex (:N))`;
             `center_e:candle_analytic_expr`;
             `box_e:candle_analytic_expr`]
            candle_q_dim_analytic_contains_certificate_transport)
          (ASSUME
            `candle_analytic_erase_sqrt_certificates center_e =
             candle_analytic_erase_sqrt_certificates box_e`))
        (ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) center_e`) in
    let center_regular_box_e =
      EQ_MP
        (MATCH_MP
          (ISPECL
            [`center_e:candle_analytic_expr`;
             `box_e:candle_analytic_expr`;
             `list_of_seq
               (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
               (dimindex (:N))`]
            candle_analytic_regular_certificate_transport)
          (ASSUME
            `candle_analytic_erase_sqrt_certificates center_e =
             candle_analytic_erase_sqrt_certificates box_e`))
        (ASSUME
          `candle_analytic_regular_at
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) center_e`) in
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC
      candle_q_dim_analytic_taylor_model_proxy_contains_regular THEN
    ASM_REWRITE_TAC[center_contains_box_e; center_regular_box_e]]);;

let candle_q_dim_taylor_model_proxy_neg_hessian = prove
 (`!result.
     candle_q_dim_jet_hessian
       (candle_q_dim_jet_normalized_neg
         (candle_q_dim_taylor_model_proxy result)) =
     candle_q_dim_interval_matrix_neg
       (candle_q_dim_taylor_model_result_hessian result)`,
  REWRITE_TAC[candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_result_neg_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_neg
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         result)
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_neg_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_neg_hessian] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_q_dim_taylor_model_proxy_add_hessian = prove
 (`!left right.
     candle_q_dim_jet_hessian
       (candle_q_dim_jet_normalized_add
         (candle_q_dim_taylor_model_proxy left)
         (candle_q_dim_taylor_model_proxy right)) =
     candle_q_dim_interval_matrix_add_normalized
       (candle_q_dim_taylor_model_result_hessian left)
       (candle_q_dim_taylor_model_result_hessian right)`,
  REWRITE_TAC[candle_q_dim_jet_normalized_add_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_result_add_analytic_invariant = prove
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
       type_witness boxes left center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes right center_b box_b
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_add
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_add center_a center_b)
       (Candle_analytic_add box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
    (fun right_th ->
      POP_ASSUM
        (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_add_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_add_hessian] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "left_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "left_box_contains_all") THEN
    USE_THEN "right_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "right_box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_add_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_add_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_add_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "left_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      USE_THEN "right_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_add_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def]]]);;

let candle_q_dim_taylor_model_result_mul_analytic_invariant = prove
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
       type_witness boxes left center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes right center_b box_b
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
    (fun right_th ->
      POP_ASSUM
        (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_mul_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "left_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "left_box_contains_all") THEN
    USE_THEN "right_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "right_box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      ASM_REWRITE_TAC[candle_analytic_regular_at_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "left_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      USE_THEN "right_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def]]]);;

let candle_q_dim_taylor_model_result_square_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_square
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         result)
       (Candle_analytic_square center_e) (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes
      (candle_q_dim_taylor_model_result_square
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        result)
      (Candle_analytic_mul center_e center_e)
      (Candle_analytic_mul box_e box_e)`
   MP_TAC THENL
   [REWRITE_TAC[candle_q_dim_taylor_model_result_square_def] THEN
    MATCH_MP_TAC candle_q_dim_taylor_model_result_mul_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
                candle_analytic_regular_at_def;
                candle_q_dim_analytic_contains_def;
                candle_analytic_value_def;
                candle_analytic_d_def;
                candle_analytic_dd_def]]);;

let candle_q_dim_taylor_model_result_inv_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_inv
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         result)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_inv_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MP_TAC
          (ASSUME
            `candle_q_dim_analytic_contains (dimindex (:N))
              (candle_q_dim_taylor_model_result_center result)
              (list_of_seq
                (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
                (dimindex (:N))) center_e`) THEN
        REWRITE_TAC[candle_q_dim_analytic_contains_def;
                    candle_q_dim_jet_contains_components_def;
                    candle_q_dim_jet_inv_domain_def] THEN
        ASM_MESON_TAC[candle_q_interval_not_zero_contains_nonzero]];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      let regular_at_p =
        MATCH_MP
          (SPEC `p:real^N`
            (ASSUME
              `!(p:real^N). p IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]
                ==> candle_analytic_regular_at
                      (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
                      box_e`))
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      let contains_at_p =
        MATCH_MP
          (SPEC `p:real^N`
            (ASSUME
              `!(p:real^N). p IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]
                ==> candle_q_dim_analytic_contains (dimindex (:N))
                      (candle_q_dim_taylor_model_proxy result)
                      (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
                      box_e`))
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [ACCEPT_TAC regular_at_p;
        MP_TAC contains_at_p THEN
        REWRITE_TAC[candle_q_dim_analytic_contains_def;
                    candle_q_dim_jet_contains_components_def;
                    candle_q_dim_jet_inv_domain_def] THEN
        ASM_MESON_TAC[candle_q_interval_not_zero_contains_nonzero]];
      MATCH_MP_TAC candle_q_dim_jet_inv_shape THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_inv_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_inv_shape THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      let contains_at_p =
        MATCH_MP
          (SPEC `p:real^N`
            (ASSUME
              `!(p:real^N). p IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]
                ==> candle_q_dim_analytic_contains (dimindex (:N))
                      (candle_q_dim_taylor_model_proxy result)
                      (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
                      box_e`))
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_inv_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def;
                      contains_at_p]]]);;

end;;
