(* ========================================================================== *)
(* Semantic invariant for the reflected centered Taylor-model interpreter.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Representation correctness is sealed in the  *)
(* preceding checkpoint.  This layer proves that completion preserves the    *)
(* center jet and whole-box Hessian before discharging the value/gradient     *)
(* Taylor reconstruction obligations and then lifting the invariant through  *)
(* the complete paired analytic program.                                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_representation.ml";;
needs "candle/cv_compute_analytic_expr_taylor_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_semantics = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_sound;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;

let candle_q_list_real_vector_def = new_definition
 `candle_q_list_real_vector qs : real^N =
    lambda i. candle_q_real (EL (i - 1) qs)`;;

let candle_q_list_real_vector_component = prove
 (`!qs i.
     1 <= i /\ i <= dimindex (:N)
     ==> (candle_q_list_real_vector qs : real^N)$i =
         candle_q_real (EL (i - 1) qs)`,
  SIMP_TAC[candle_q_list_real_vector_def; LAMBDA_BETA]);;

(* The executable uses outward-rounded radii.  Record the structural and     *)
(* order facts once; later Taylor arguments can use the rounded list without *)
(* reopening the scalar floor/ceiling implementation.                        *)

let candle_q_fixed_list_round_upper_length = prove
 (`!items.
     LENGTH (candle_q_fixed_list_round_upper items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_def; LENGTH]);;

let candle_q_fixed_list_round_upper_map = prove
 (`!items.
     candle_q_fixed_list_round_upper items =
     MAP candle_q_fixed_round_upper items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_def; MAP]);;

let candle_q_fixed_list_round_upper_el = prove
 (`!items i.
     i < LENGTH items
     ==> EL i (candle_q_fixed_list_round_upper items) =
         candle_q_fixed_round_upper (EL i items)`,
  SIMP_TAC[candle_q_fixed_list_round_upper_map; EL_MAP]);;

let candle_q_fixed_list_round_upper_nonnegative = prove
 (`!items.
     ALL (\q. &0 <= candle_q_real q) items
     ==> ALL (\q. &0 <= candle_q_real q)
           (candle_q_fixed_list_round_upper items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_def; ALL] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `candle_q_real h` THEN
    ASM_REWRITE_TAC[candle_q_fixed_round_upper_sound];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_q_fixed_list_round_upper_m_cell_domain = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     m_cell_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_center_vector boxes)
       (candle_q_list_real_vector
         (candle_q_fixed_list_round_upper
           (candle_q_radius_list boxes)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_cell_domain] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(candle_q_box_lower_vector boxes : real^N)$i <=
      (candle_q_box_center_vector boxes : real^N)$i /\
    (candle_q_box_center_vector boxes : real^N)$i <=
      (candle_q_box_upper_vector boxes : real^N)$i /\
    max
      ((candle_q_box_center_vector boxes : real^N)$i -
       (candle_q_box_lower_vector boxes : real^N)$i)
      ((candle_q_box_upper_vector boxes : real^N)$i -
       (candle_q_box_center_vector boxes : real^N)$i) <=
      (candle_q_box_radius_vector boxes : real^N)$i`
   STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ISPEC
        `boxes:(((num#num)#num)#((num#num)#num))list`
        candle_q_box_m_cell_domain) THEN
    ASM_REWRITE_TAC[m_cell_domain] THEN
    DISCH_THEN (MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(candle_q_box_radius_vector boxes : real^N)$i` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(candle_q_list_real_vector
       (candle_q_fixed_list_round_upper
         (candle_q_radius_list boxes)) : real^N)$i =
    candle_q_real
      (EL (i - 1)
        (candle_q_fixed_list_round_upper
          (candle_q_radius_list boxes)))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_list_real_vector_component THEN
    UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EL (i - 1)
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) =
    candle_q_fixed_round_upper
      (EL (i - 1) (candle_q_radius_list boxes))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_fixed_list_round_upper_el THEN
    ASM_REWRITE_TAC[candle_q_radius_list_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (EL (i - 1) (candle_q_radius_list boxes)) =
    (candle_q_box_radius_vector boxes : real^N)$i`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_radius_list_vector_component THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPEC `EL (i - 1) (candle_q_radius_list boxes)`
      candle_q_fixed_round_upper_sound) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dot_list_real_vector_sum = prove
 (`!radii (g:num->real).
     LENGTH radii = dimindex (:N)
     ==>
     ITLIST2
       (\r y total. candle_q_real r * abs y + total)
       radii (list_of_seq g (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            abs (g (i - 1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`\r y. candle_q_real r * abs y`;
       `radii:((num#num)#num)list`;
       `list_of_seq (g:num->real) (dimindex (:N))`]
      candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[candle_q_list_real_vector_component;
                 EL_LIST_OF_SEQ]]);;

let candle_q_weighted_rows_list_real_vector_sum = prove
 (`!radii (h:num->num->real).
     LENGTH radii = dimindex (:N)
     ==>
     ITLIST2
       (\w values total.
          candle_q_real w *
          ITLIST2
            (\r y subtotal. candle_q_real r * abs y + subtotal)
            radii values (&0) + total)
       radii
       (list_of_seq
         (\di. list_of_seq (h di) (dimindex (:N)))
         (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_list_real_vector radii : real^N)$j *
                   abs (h (i - 1) (j - 1))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`\w values.
         candle_q_real w *
         ITLIST2
           (\r y subtotal. candle_q_real r * abs y + subtotal)
           radii values (&0)`;
       `radii:((num#num)#num)list`;
       `list_of_seq
         (\di. list_of_seq ((h:num->num->real) di) (dimindex (:N)))
         (dimindex (:N))`]
      candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[candle_q_list_real_vector_component;
                 EL_LIST_OF_SEQ;
                 candle_q_dot_list_real_vector_sum]]);;

let candle_q_dim_jet_gradient_list_rounded_sum_bound = prove
 (`!f radii center_jet.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     candle_q_stack_contains
       (candle_q_dim_jet_gradient center_jet)
       (list_of_seq
         (\di. partial (di + 1) (f:real^N->real)
           (candle_q_box_center_vector boxes : real^N))
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            abs
              (partial i f
                (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper_extended radii
         (candle_q_dim_jet_gradient center_jet))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dot_abs_upper_extended_real] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs
             (partial i f
               (candle_q_box_center_vector boxes : real^N))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs
             (partial ((i - 1) + 1) f
               (candle_q_box_center_vector boxes : real^N)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  let values_tm =
    `list_of_seq
      (\di. partial (di + 1) (f:real^N->real)
        (candle_q_box_center_vector boxes : real^N))
      (dimindex (:N))` in
  SUBGOAL_THEN
   `ITLIST2
      (\r y total. candle_q_real r * abs y + total)
      radii
      (list_of_seq
        (\di. partial (di + 1) (f:real^N->real)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))) (&0) <=
    candle_q_real
      (candle_q_dot_abs_upper radii
        (candle_q_dim_jet_gradient center_jet))`
   (LABEL_TAC "rounded_gradient_bound") THENL
   [MATCH_MP_TAC candle_q_dot_abs_upper_sound THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ITLIST2
      (\r y total. candle_q_real r * abs y + total)
      radii
      (list_of_seq
        (\di. partial (di + 1) (f:real^N->real)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))) (&0) =
    sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs
             (partial ((i - 1) + 1) f
               (candle_q_box_center_vector boxes : real^N)))`
   (LABEL_TAC "rounded_gradient_sum") THENL
   [MATCH_MP_TAC candle_q_dot_list_real_vector_sum THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let sum_th =
    ASSUME
      `ITLIST2
        (\r y total. candle_q_real r * abs y + total)
        radii
        (list_of_seq
          (\di. partial (di + 1) (f:real^N->real)
            (candle_q_box_center_vector boxes : real^N))
          (dimindex (:N))) (&0) =
       sum (1..dimindex (:N))
        (\i. (candle_q_list_real_vector radii : real^N)$i *
             abs
               (partial ((i - 1) + 1) f
                 (candle_q_box_center_vector boxes : real^N)))` in
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ITLIST2
      (\r y total. candle_q_real r * abs y + total)
      radii
      (list_of_seq
        (\di. partial (di + 1) (f:real^N->real)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))) (&0)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[sum_th] THEN REWRITE_TAC[REAL_LE_REFL];
    MATCH_ACCEPT_TAC
      (ASSUME
        `ITLIST2
          (\r y total. candle_q_real r * abs y + total)
          radii
          (list_of_seq
            (\di. partial (di + 1) (f:real^N->real)
              (candle_q_box_center_vector boxes : real^N))
            (dimindex (:N))) (&0) <=
         candle_q_real
           (candle_q_dot_abs_upper radii
             (candle_q_dim_jet_gradient center_jet))`) ]);;

let candle_q_dim_jet_hessian_list_rounded_sum_bound = prove
 (`!f radii box_jet (z:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian box_jet)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1) (f:real^N->real) z)
           (dimindex (:N)))
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_list_real_vector radii : real^N)$j *
                   abs (partial2 j i f z))) <=
     candle_q_real
       (candle_q_weighted_rows_abs_upper_extended radii radii
         (candle_q_dim_jet_hessian box_jet))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_weighted_rows_abs_upper_extended_real] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_list_real_vector radii : real^N)$j *
                  abs (partial2 j i (f:real^N->real) z))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_list_real_vector radii : real^N)$j *
                  abs (partial2 ((j - 1) + 1) ((i - 1) + 1)
                    (f:real^N->real) z)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  let values_tm =
    `list_of_seq
      (\di. list_of_seq
        (\dj. partial2 (dj + 1) (di + 1)
          (f:real^N->real) (z:real^N))
        (dimindex (:N)))
      (dimindex (:N))` in
  SUBGOAL_THEN
   `ALL
      (\values. LENGTH (radii:((num#num)#num)list) = LENGTH values)
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1)
            (f:real^N->real) (z:real^N))
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "rounded_hessian_row_lengths") THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (radii:((num#num)#num)list) =
    LENGTH
      (list_of_seq
        (\di. list_of_seq
          (\dj. partial2 (dj + 1) (di + 1)
            (f:real^N->real) (z:real^N))
          (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "rounded_hessian_outer_lengths") THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  let bound_th =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `radii:((num#num)#num)list`; values_tm;
         `candle_q_dim_jet_hessian box_jet`]
        candle_q_weighted_rows_abs_upper_sound)
      (CONJ
        (ASSUME `ALL (\r. &0 <= candle_q_real r) radii`)
        (CONJ
          (ASSUME `ALL (\r. &0 <= candle_q_real r) radii`)
          (CONJ
            (ASSUME
              `ALL2 candle_q_stack_contains
                (candle_q_dim_jet_hessian box_jet)
                (list_of_seq
                  (\di. list_of_seq
                    (\dj. partial2 (dj + 1) (di + 1)
                      (f:real^N->real) z)
                  (dimindex (:N)))
                  (dimindex (:N)))`)
            (CONJ
              (ASSUME
                `LENGTH (radii:((num#num)#num)list) =
                 LENGTH
                   (list_of_seq
                     (\di. list_of_seq
                       (\dj. partial2 (dj + 1) (di + 1)
                         (f:real^N->real) (z:real^N))
                       (dimindex (:N)))
                     (dimindex (:N)))`)
              (ASSUME
                `ALL
                  (\values.
                    LENGTH (radii:((num#num)#num)list) = LENGTH values)
                  (list_of_seq
                    (\di. list_of_seq
                      (\dj. partial2 (dj + 1) (di + 1)
                        (f:real^N->real) (z:real^N))
                      (dimindex (:N)))
                    (dimindex (:N)))`))))) in
  let sum_th =
    BETA_RULE
      (MATCH_MP
        (ISPECL [`radii:((num#num)#num)list`;
                  `\di dj. partial2 (dj + 1) (di + 1)
                    (f:real^N->real) (z:real^N)`]
          candle_q_weighted_rows_list_real_vector_sum)
        (ASSUME
          `LENGTH (radii:((num#num)#num)list) = dimindex (:N)`)) in
  ACCEPT_TAC
    (EQ_MP
      (BETA_RULE
        (AP_TERM
          `\x:real.
             x <= candle_q_real
               (candle_q_weighted_rows_abs_upper radii radii
                 (candle_q_dim_jet_hessian box_jet))`
          sum_th))
      bound_th));;

let candle_q_dim_analytic_jet_rounded_gradient_sum_bound = prove
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
    ASM_REWRITE_TAC[] THEN
    let center_contains_th =
      MATCH_MP
        (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
          candle_q_box_center_stack_contains)
        (ASSUME `candle_q_box_valid_list boxes`) in
    let center_list_th =
      MATCH_MP
        (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
          candle_q_box_center_vector_list)
        (ASSUME
          `LENGTH
            (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`) in
    MATCH_MP_TAC candle_q_dim_analytic_domain_regular THEN
    EXISTS_TAC `boxes:(((num#num)#num)#((num#num)#num))list` THEN
    ASM_REWRITE_TAC[center_list_th; center_contains_th]]);;

let candle_q_dim_analytic_jet_rounded_m_taylor_error_sound = prove
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
       (candle_q_list_real_vector
         (candle_q_fixed_list_round_upper
           (candle_q_radius_list boxes)))
       (candle_q_real
         (candle_q_weighted_rows_abs_upper_extended
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           (candle_q_dim_jet_hessian box_jet)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  MATCH_MP_TAC candle_q_dim_jet_hessian_list_rounded_sum_bound THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_length;
                    candle_q_radius_list_length];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_fixed_list_round_upper_nonnegative THEN
      MATCH_MP_TAC candle_q_radius_list_nonnegative THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_dim_analytic_jet_hessian_flyspeck_contains THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_dim_analytic_domain_regular THEN
        EXISTS_TAC `boxes:(((num#num)#num)#((num#num)#num))list` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC candle_q_box_stack_contains_vector THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]]]]);;

let candle_q_dim_taylor_model_error_real = prove
 (`!radii center_jet hessian.
     candle_q_real
       (candle_q_dim_taylor_model_error radii center_jet hessian) =
     candle_q_real
       (candle_q_dot_abs_upper_extended radii
         (candle_q_dim_jet_gradient center_jet)) +
     inv (&2) *
       candle_q_real
         (candle_q_weighted_rows_abs_upper_extended
           radii radii hessian)`,
  REWRITE_TAC[candle_q_dim_taylor_model_error_def;
              candle_q_real_add_normalized_extended;
              candle_q_real_mul_normalized_extended;
              candle_q_real_half]);;

let candle_q_dim_taylor_model_value_bound_real = prove
 (`!radii center_jet hessian.
     candle_q_real
       (FST
         (candle_q_dim_taylor_model_value_bound
           radii center_jet hessian)) =
       candle_q_real (FST (candle_q_dim_jet_f center_jet)) -
       candle_q_real
         (candle_q_dim_taylor_model_error radii center_jet hessian) /\
     candle_q_real
       (SND
         (candle_q_dim_taylor_model_value_bound
           radii center_jet hessian)) =
       candle_q_real (SND (candle_q_dim_jet_f center_jet)) +
       candle_q_real
         (candle_q_dim_taylor_model_error radii center_jet hessian)`,
  REWRITE_TAC[candle_q_dim_taylor_model_value_bound_def;
              candle_q_interval_add_extended_def;
              candle_q_symmetric_interval_def;
              candle_q_dim_jet_f_def;
              candle_q_real_add_normalized_extended;
              candle_q_real_neg; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_q_dim_first_jet_fixed_round_analytic_contains = prove
 (`!n jet env e.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_analytic_contains n jet env e
     ==> candle_q_dim_analytic_contains n
           (candle_q_dim_first_jet_fixed_round jet) env e`,
  REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
  MATCH_ACCEPT_TAC candle_q_dim_first_jet_fixed_round_contains_components);;

let candle_q_dim_analytic_jet_complete_m_taylor_error_sound = prove
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
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_analytic_domain_regular THEN
      EXISTS_TAC `boxes:(((num#num)#num)#((num#num)#num))list` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC candle_q_box_stack_contains_vector THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
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

let candle_q_dim_analytic_taylor_model_value_bound_contains = prove
 (`!e boxes center_jet box_jet (p:real^N).
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
   [MATCH_MP_TAC candle_q_dim_analytic_diff2_domain THEN
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
    MATCH_MP_TAC candle_q_dim_analytic_jet_complete_m_taylor_error_sound THEN
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
      MATCH_MP_TAC candle_q_dim_analytic_jet_rounded_gradient_sum_bound THEN
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

let candle_q_dim_taylor_model_gradient_bounds_map2 = prove
 (`!radii gradients rows.
     LENGTH gradients = LENGTH rows
     ==>
     candle_q_dim_taylor_model_gradient_bounds radii gradients rows =
     MAP2
       (\gradient_interval interval_row.
          candle_q_interval_add_extended gradient_interval
            (candle_q_symmetric_interval
              (candle_q_dot_abs_upper_extended radii interval_row)))
       gradients rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; candle_q_dim_taylor_model_gradient_bounds_def;
                MAP2_DEF] THEN ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; candle_q_dim_taylor_model_gradient_bounds_def;
                  MAP2_DEF; CONS_11] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[HD; TL; SUC_INJ] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let candle_q_dim_taylor_model_gradient_bounds_el = prove
 (`!radii gradients rows i.
     LENGTH gradients = LENGTH rows /\ i < LENGTH gradients
     ==>
     EL i (candle_q_dim_taylor_model_gradient_bounds radii gradients rows) =
     candle_q_interval_add_extended (EL i gradients)
       (candle_q_symmetric_interval
         (candle_q_dot_abs_upper_extended radii (EL i rows)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_taylor_model_gradient_bounds_map2] THEN
  MATCH_MP_TAC EL_MAP2 THEN ASM_ARITH_TAC);;

let candle_q_interval_add_symmetric_real = prove
 (`!center radius.
     candle_q_real
       (FST
         (candle_q_interval_add_extended center
           (candle_q_symmetric_interval radius))) =
       candle_q_real (FST center) - candle_q_real radius /\
     candle_q_real
       (SND
         (candle_q_interval_add_extended center
           (candle_q_symmetric_interval radius))) =
       candle_q_real (SND center) + candle_q_real radius`,
  REWRITE_TAC[candle_q_interval_add_extended_def;
              candle_q_symmetric_interval_def;
              candle_q_real_add_normalized_extended;
              candle_q_real_neg; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_all2_el_right = prove
 (`!P xs ys i.
     ALL2 P xs ys /\ i < LENGTH ys
     ==> P (EL i xs) (EL i ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; LENGTH; LT];
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[ALL2];
      INDUCT_TAC THEN
      ASM_REWRITE_TAC[ALL2; LENGTH; EL; HD; TL; LT_SUC] THEN
      ASM_MESON_TAC[]]]);;

let candle_all2_right_list_of_seq_el = prove
 (`!P xs n (g:num->B) i.
     ALL2 P xs (list_of_seq g n) /\ i < n
     ==> P (EL i xs) (g i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `EL i (list_of_seq (g:num->B) n) = g i`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_all2_el_right THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]]);;

let candle_q_dim_analytic_jet_complete_partial_error_sound = prove
 (`!e boxes box_jet i.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_q_dim_analytic_domain boxes e /\
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
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_analytic_domain_regular THEN
      EXISTS_TAC `boxes:(((num#num)#num)#((num#num)#num))list` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC candle_q_box_stack_contains_vector THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
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


(* Rounding is shape preserving for the complete Hessian matrix. *)

let candle_q_fixed_interval_matrix_round_length = prove
 (`!rows.
     LENGTH (candle_q_fixed_interval_matrix_round rows) = LENGTH rows`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_interval_matrix_round_def; LENGTH]);;

let candle_q_fixed_interval_matrix_round_rows_width = prove
 (`!n rows.
     candle_q_dim_interval_rows_width n rows
     ==> candle_q_dim_interval_rows_width n
           (candle_q_fixed_interval_matrix_round rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_fixed_interval_matrix_round_def];
    REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_fixed_interval_matrix_round_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_q_fixed_interval_list_round_length];
      ASM_MESON_TAC[]]]);;

let candle_q_fixed_interval_matrix_round_shape = prove
 (`!n rows.
     candle_q_dim_interval_matrix_shape n rows
     ==> candle_q_dim_interval_matrix_shape n
           (candle_q_fixed_interval_matrix_round rows)`,
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  MESON_TAC[candle_q_fixed_interval_matrix_round_length;
            candle_q_fixed_interval_matrix_round_rows_width]);;

let candle_q_dim_taylor_model_gradient_bounds_length = prove
 (`!radii gradients rows.
     LENGTH gradients = LENGTH rows
     ==> LENGTH
           (candle_q_dim_taylor_model_gradient_bounds
             radii gradients rows) = LENGTH gradients`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_gradient_bounds_def; LENGTH];
    X_GEN_TAC
      `row_lists:((((num#num)#num)#((num#num)#num))list)list` THEN
    MP_TAC
      (ISPEC
        `row_lists:((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_q_dim_taylor_model_gradient_bounds_def;
                    LENGTH; SUC_INJ; NOT_SUC]]);;

(* Completion rounds but does not change the authenticated center jet or     *)
(* whole-box Hessian semantics.  Value and gradient reconstruction are the   *)
(* remaining analytic part of the invariant.                                 *)

let candle_q_dim_taylor_model_result_complete_center_shape = prove
 (`!n radii domain center_jet box_jet.
     candle_q_dim_jet_shape n center_jet
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_taylor_model_result_center
             (candle_q_dim_taylor_model_result_complete radii domain
               center_jet (candle_q_dim_jet_hessian box_jet)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_first_jet_fixed_round_shape);;

let candle_q_dim_taylor_model_result_complete_center_contains = prove
 (`!n radii domain center_jet box_jet value gradient hessian.
     candle_q_dim_jet_shape n center_jet /\
     candle_q_dim_jet_contains_components
       n center_jet value gradient hessian
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_taylor_model_result_center
             (candle_q_dim_taylor_model_result_complete radii domain
               center_jet (candle_q_dim_jet_hessian box_jet)))
           value gradient hessian`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_first_jet_fixed_round_contains_components);;

let candle_q_dim_taylor_model_proxy_make_shape = prove
 (`!n domain center value gradients hessian.
     LENGTH gradients = n /\
     candle_q_dim_interval_matrix_shape n hessian
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_taylor_model_proxy
             (candle_q_dim_taylor_model_result_make
               domain center value gradients hessian))`,
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_shape_def; candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def; candle_q_dim_jet_hessian_def;
              FST; SND]);;

let candle_q_dim_taylor_model_result_complete_proxy_shape = prove
 (`!n radii domain center_jet box_jet.
     candle_q_dim_jet_shape n center_jet /\
     candle_q_dim_jet_shape n box_jet
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_taylor_model_proxy
             (candle_q_dim_taylor_model_result_complete radii domain
               center_jet (candle_q_dim_jet_hessian box_jet)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape n
      (candle_q_dim_first_jet_fixed_round center_jet)`
   (LABEL_TAC "rounded_center_shape") THENL
   [MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_interval_matrix_shape n
      (candle_q_fixed_interval_matrix_round
        (candle_q_dim_jet_hessian box_jet))`
   (LABEL_TAC "rounded_hessian_shape") THENL
   [MATCH_MP_TAC candle_q_fixed_interval_matrix_round_shape THEN
    ASM_MESON_TAC[candle_q_dim_jet_shape_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_dim_taylor_model_gradient_bounds radii
        (candle_q_dim_jet_gradient
          (candle_q_dim_first_jet_fixed_round center_jet))
        (candle_q_fixed_interval_matrix_round
          (candle_q_dim_jet_hessian box_jet))) = n`
   (LABEL_TAC "reconstructed_gradient_length") THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `LENGTH
        (candle_q_dim_jet_gradient
          (candle_q_dim_first_jet_fixed_round center_jet))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_taylor_model_gradient_bounds_length THEN
      ASM_MESON_TAC[candle_q_dim_jet_shape_def;
                    candle_q_dim_interval_matrix_shape_def];
      ASM_MESON_TAC[candle_q_dim_jet_shape_def]];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_proxy_make_shape THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_fixed_interval_list_round_length] THEN
    ACCEPT_TAC
      (ASSUME
        `LENGTH
          (candle_q_dim_taylor_model_gradient_bounds radii
            (candle_q_dim_jet_gradient
              (candle_q_dim_first_jet_fixed_round center_jet))
            (candle_q_fixed_interval_matrix_round
              (candle_q_dim_jet_hessian box_jet))) = n`);
    ACCEPT_TAC
      (ASSUME
        `candle_q_dim_interval_matrix_shape n
          (candle_q_fixed_interval_matrix_round
            (candle_q_dim_jet_hessian box_jet))`)]);;

let candle_q_dim_taylor_model_result_complete_proxy_hessian_contains = prove
 (`!n radii domain center_jet box_jet value gradient hessian.
     candle_q_dim_jet_shape n box_jet /\
     candle_q_dim_jet_contains_components
       n box_jet value gradient hessian
     ==> ALL2 candle_q_stack_contains
           (candle_q_dim_jet_hessian
             (candle_q_dim_taylor_model_proxy
               (candle_q_dim_taylor_model_result_complete radii domain
                 center_jet (candle_q_dim_jet_hessian box_jet))))
           (list_of_seq
             (\di. list_of_seq (\dj. hessian di dj) n) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
              FST; SND] THEN
  MATCH_MP_TAC candle_q_fixed_interval_matrix_round_contains THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_hessian box_jet =
    list_of_seq
      (\di. list_of_seq
        (\dj. candle_q_dim_jet_hessian_at box_jet di dj) n) n`
   (LABEL_TAC "hessian_sequence") THENL
   [MATCH_MP_TAC candle_q_dim_jet_hessian_list_of_seq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM candle_q_dim_jet_hessian_def] THEN
  ONCE_REWRITE_TAC
    [ASSUME
      `candle_q_dim_jet_hessian box_jet =
       list_of_seq
         (\di. list_of_seq
           (\dj. candle_q_dim_jet_hessian_at box_jet di dj) n) n`] THEN
  REWRITE_TAC[candle_all2_list_of_seq;
              candle_q_stack_contains_all2] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]) THEN
  ASM_SIMP_TAC[]);;

end;;
