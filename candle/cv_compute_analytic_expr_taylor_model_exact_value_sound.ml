(* ========================================================================== *)
(* Scale-independent exact-rational Taylor value handoff.                    *)
(*                                                                            *)
(* The packed checker computes at scale 2^40, while the older reflected      *)
(* completion rounded through a 10^12 representation.  The common semantic  *)
(* boundary is therefore the exact [candle_q] value before either encoding.  *)
(* This file proves that boundary for arbitrary nonnegative rational radii,  *)
(* an arbitrary Taylor center, and an arbitrary full Hessian enclosure.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_semantics.ml";;

module Candle_cv_analytic_expr_taylor_model_exact_value_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;

let candle_q_exact_gradient_sum_bound = prove
 (`!(f:real^N->real) (y:real^N) radii gradient.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     candle_q_stack_contains gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            abs (partial i f y)) <=
     candle_q_real (candle_q_dot_abs_upper_extended radii gradient)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dot_abs_upper_extended_real] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs (partial i (f:real^N->real) y)) =
    sum (1..dimindex (:N))
      (\i. (candle_q_list_real_vector radii : real^N)$i *
           abs (partial ((i - 1) + 1) f y))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  let sum_th =
    BETA_RULE
      (MATCH_MP
        (ISPECL
          [`radii:((num#num)#num)list`;
           `\di. partial (di + 1) (f:real^N->real) (y:real^N)`]
          candle_q_dot_list_real_vector_sum)
        (ASSUME
          `LENGTH (radii:((num#num)#num)list) = dimindex (:N)`)) in
  ONCE_REWRITE_TAC[GSYM sum_th] THEN
  MATCH_MP_TAC candle_q_dot_abs_upper_sound THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

let candle_q_exact_hessian_m_taylor_error = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) radii hessian.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N))))
     ==>
     m_taylor_error f (lower,upper)
       (candle_q_list_real_vector radii)
       (candle_q_real
         (candle_q_weighted_rows_abs_upper_extended
           radii radii hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  MP_TAC
    (ISPECL
      [`f:real^N->real`; `radii:((num#num)#num)list`;
       `candle_q_dim_jet_make candle_q_zero_interval [] hessian`;
       `z:real^N`]
      candle_q_dim_jet_hessian_list_rounded_sum_bound) THEN
  REWRITE_TAC[candle_q_dim_jet_make_def;
              candle_q_dim_jet_hessian_def; FST; SND] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let candle_q_interval_arith_contains = prove
 (`!(i:((num#num)#num)#((num#num)#num)) x.
     interval_arith x
       (candle_q_real (FST i),candle_q_real (SND i)) <=>
     candle_q_interval_contains i x`,
  REWRITE_TAC[Interval_arith.interval_arith;
              candle_q_interval_contains_def]);;

let candle_q_dim_jet_f_make = prove
 (`!value gradient hessian.
     candle_q_dim_jet_f
       (candle_q_dim_jet_make value gradient hessian) = value`,
  REWRITE_TAC[candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def; FST; SND]);;

let candle_q_exact_taylor_error_bound = prove
 (`!(f:real^N->real) (y:real^N) radii
       center_value center_gradient hessian.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            abs (partial i f y)) +
     candle_q_real
       (candle_q_weighted_rows_abs_upper_extended
         radii radii hessian) / &2 <=
     candle_q_real
       (candle_q_dim_taylor_model_error radii
         (candle_q_dim_jet_make center_value center_gradient hessian)
         hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let gradient_th =
      MATCH_MP
        (ISPECL
          [`f:real^N->real`; `y:real^N`;
           `radii:((num#num)#num)list`;
           `center_gradient:
              (((num#num)#num)#((num#num)#num))list`]
          candle_q_exact_gradient_sum_bound)
        (CONJ
          (ASSUME
            `LENGTH (radii:((num#num)#num)list) = dimindex (:N)`)
          (CONJ
            (ASSUME `ALL (\r. &0 <= candle_q_real r) radii`)
            (ASSUME
              `candle_q_stack_contains center_gradient
                (list_of_seq
                  (\di. partial (di + 1) (f:real^N->real) (y:real^N))
                  (dimindex (:N)))`))) in
  MP_TAC gradient_th THEN
  REWRITE_TAC[candle_q_dim_taylor_model_error_real;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def; FST; SND; real_div] THEN
  REAL_ARITH_TAC);;

let candle_q_exact_taylor_value_bound_from_components = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii center_value center_gradient hessian (p:real^N).
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     m_taylor_error f (lower,upper)
       (candle_q_list_real_vector radii)
       (candle_q_real
         (candle_q_weighted_rows_abs_upper_extended
           radii radii hessian)) /\
     interval_arith (f y)
       (candle_q_real (FST center_value),
        candle_q_real (SND center_value)) /\
     sum (1..dimindex (:N))
       (\i. (candle_q_list_real_vector radii : real^N)$i *
            abs (partial i f y)) +
     candle_q_real
       (candle_q_weighted_rows_abs_upper_extended
         radii radii hessian) / &2 <=
     candle_q_real
       (candle_q_dim_taylor_model_error radii
         (candle_q_dim_jet_make center_value center_gradient hessian)
         hessian) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_dim_taylor_model_value_bound radii
       (candle_q_dim_jet_make center_value center_gradient hessian)
         hessian)
       (f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let bounds_th =
      ISPECL
        [`((lower:real^N),(upper:real^N))`;
         `y:real^N`;
         `(candle_q_list_real_vector radii : real^N)`;
         `f:real^N->real`;
         `candle_q_real
           (candle_q_weighted_rows_abs_upper_extended
             radii radii hessian)`;
         `candle_q_real (FST center_value)`;
         `candle_q_real (SND center_value)`;
         `candle_q_real
            (candle_q_dim_taylor_model_error radii
              (candle_q_dim_jet_make
                center_value center_gradient hessian)
              hessian)`;
         `candle_q_real
            (FST
              (candle_q_dim_taylor_model_value_bound radii
                (candle_q_dim_jet_make
                  center_value center_gradient hessian)
                hessian))`;
         `candle_q_real
            (SND
              (candle_q_dim_taylor_model_value_bound radii
                (candle_q_dim_jet_make
                  center_value center_gradient hessian)
                hessian))`]
        m_taylor_bounds in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_cell_domain (lower,upper) (y:real^N)
            (candle_q_list_real_vector radii)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME `diff2_domain (lower,upper) (f:real^N->real)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_taylor_error (f:real^N->real)
            ((lower:real^N),(upper:real^N))
            (candle_q_list_real_vector radii : real^N)
            (candle_q_real
              (candle_q_weighted_rows_abs_upper_extended
                radii radii hessian))`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `interval_arith ((f:real^N->real) (y:real^N))
            (candle_q_real (FST center_value),
             candle_q_real (SND center_value))`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `sum (1..dimindex (:N))
             (\i. (candle_q_list_real_vector radii : real^N)$i *
                  abs (partial i (f:real^N->real) (y:real^N))) +
           candle_q_real
             (candle_q_weighted_rows_abs_upper_extended
               radii radii hessian) / &2 <=
           candle_q_real
             (candle_q_dim_taylor_model_error radii
               (candle_q_dim_jet_make
                 center_value center_gradient hessian)
               hessian)`) in
  let value_real_th =
      SPECL
        [`radii:((num#num)#num)list`;
         `candle_q_dim_jet_make center_value center_gradient hessian`;
         `hessian:
            ((((num#num)#num)#((num#num)#num))list)list`]
        candle_q_dim_taylor_model_value_bound_real in
  let value_real_th =
      REWRITE_RULE
        [candle_q_dim_jet_f_make]
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
  let point_th =
      MATCH_MP
        (SPEC `p:real^N`
          (REWRITE_RULE[m_bounded_on_int] bounded_th))
        (ASSUME
          `(p:real^N) IN interval [(lower:real^N),(upper:real^N)]`) in
  let contains_th =
      EQ_MP
        (SPECL
          [`candle_q_dim_taylor_model_value_bound radii
              (candle_q_dim_jet_make
                center_value center_gradient hessian)
              hessian`;
           `(f:real^N->real) (p:real^N)`]
          candle_q_interval_arith_contains)
        point_th in
  MATCH_ACCEPT_TAC contains_th);;

let candle_q_exact_taylor_value_bound_contains = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii center_value center_gradient hessian (p:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_q_interval_contains center_value (f y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_dim_taylor_model_value_bound radii
       (candle_q_dim_jet_make center_value center_gradient hessian)
         hessian)
       (f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
   (ISPECL
     [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
      `radii:((num#num)#num)list`;
      `center_value:((num#num)#num)#((num#num)#num)`;
      `center_gradient:
         (((num#num)#num)#((num#num)#num))list`;
      `hessian:
         ((((num#num)#num)#((num#num)#num))list)list`;
      `p:real^N`]
     candle_q_exact_taylor_value_bound_from_components) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_exact_hessian_m_taylor_error THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `candle_q_interval_contains center_value (f (y:real^N))` THEN
    REWRITE_TAC[candle_q_interval_contains_def;
                Interval_arith.interval_arith];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_exact_taylor_error_bound THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

if hyp candle_q_exact_gradient_sum_bound <> [] ||
   hyp candle_q_exact_hessian_m_taylor_error <> [] ||
   hyp candle_q_interval_arith_contains <> [] ||
   hyp candle_q_dim_jet_f_make <> [] ||
   hyp candle_q_exact_taylor_error_bound <> [] ||
   hyp candle_q_exact_taylor_value_bound_from_components <> [] ||
   hyp candle_q_exact_taylor_value_bound_contains <> [] then
  failwith "exact-rational Taylor value soundness: assumptions";;

print_endline
  "CANDLE_CV_EXACT_TAYLOR_VALUE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
