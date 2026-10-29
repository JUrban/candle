(* ========================================================================== *)
(* Scale-independent exact-rational Taylor gradient handoff.                 *)
(*                                                                            *)
(* The packed checker supplies arbitrary authenticated nonnegative radii.     *)
(* This file proves that the completed gradient rows enclose the exact first  *)
(* partials throughout an arbitrary Taylor cell.  It is the gradient analogue *)
(* of [candle_q_exact_taylor_value_bound_contains].                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_exact_value_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_exact_gradient_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_exact_value_sound;;
open Candle_cv_analytic_expr_taylor_model_invariant;;

let candle_q_exact_hessian_m_taylor_partial_error = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) radii hessian i.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     i IN 1..dimindex (:N)
     ==>
     m_taylor_partial_error f i (lower,upper)
       (candle_q_list_real_vector radii)
       (candle_q_real
         (candle_q_dot_abs_upper_extended radii (EL (i - 1) hessian)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_partial_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_stack_contains (EL (i - 1) hessian)
      (list_of_seq
        (\dj. partial2 (dj + 1) i (f:real^N->real) (z:real^N))
        (dimindex (:N)))`
   (LABEL_TAC "row_contains") THENL
   [MP_TAC
      (ISPECL
        [`candle_q_stack_contains`;
         `hessian:
            ((((num#num)#num)#((num#num)#num))list)list`;
         `dimindex (:N)`;
         `\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (f:real^N->real) (z:real^N))
           (dimindex (:N))`;
         `i - 1`]
        candle_all2_right_list_of_seq_el) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  MP_TAC
    (ISPECL
      [`partial i (f:real^N->real)`; `z:real^N`;
       `radii:((num#num)#num)list`;
       `EL (i - 1)
          (hessian:
            ((((num#num)#num)#((num#num)#num))list)list)`]
      candle_q_exact_gradient_sum_bound) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM partial2] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_ACCEPT_TAC]);;

let candle_q_exact_taylor_gradient_component_contains = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii center_gradient hessian (p:real^N) i.
     LENGTH radii = dimindex (:N) /\
     LENGTH center_gradient = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
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
     i IN 1..dimindex (:N) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_fixed_interval_round
         (EL (i - 1)
           (candle_q_dim_taylor_model_gradient_bounds
             radii center_gradient hessian)))
       (partial i f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  let center_lookup_th =
    MATCH_MP
      (SPECL
        [`i - 1`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `list_of_seq
            (\di. partial (di + 1) (f:real^N->real) (y:real^N))
            (dimindex (:N))`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains center_gradient
          (list_of_seq
            (\di. partial (di + 1) (f:real^N->real) (y:real^N))
            (dimindex (:N)))`) in
  let center_interval_lookup_th =
    MATCH_MP
      (SPECL
        [`center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `i - 1`]
        candle_q_interval_lookup_in_range)
      (REWRITE_RULE
        [GSYM (ASSUME
          `LENGTH
             (center_gradient:
               (((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)]
        (ASSUME `i - 1 < dimindex (:N)`)) in
  let center_real_lookup_th =
    MATCH_MP
      (ISPECL
        [`\di. partial (di + 1) (f:real^N->real) (y:real^N)`;
         `dimindex (:N)`; `i - 1`]
        candle_q_real_lookup_list_of_seq)
      (ASSUME `i - 1 < dimindex (:N)`) in
  let center_contains_th =
    REWRITE_RULE
      [center_interval_lookup_th; center_real_lookup_th;
       ASSUME `(i - 1) + 1 = i`]
      center_lookup_th in
  ASSUME_TAC center_contains_th THEN
  ABBREV_TAC
   `(center_interval:
       ((num#num)#num)#((num#num)#num)) = EL (i - 1) center_gradient` THEN
  ABBREV_TAC
   `(partial_error_q:(num#num)#num) =
      candle_q_dot_abs_upper_extended radii (EL (i - 1) hessian)` THEN
  ABBREV_TAC
   `(gradient_bound:
       ((num#num)#num)#((num#num)#num)) =
      candle_q_interval_add_extended center_interval
        (candle_q_symmetric_interval partial_error_q)` THEN
  SUBGOAL_THEN
   `EL (i - 1)
      (candle_q_dim_taylor_model_gradient_bounds
        radii center_gradient hessian) = gradient_bound`
   (LABEL_TAC "gradient_bound_el") THENL
   [MP_TAC
      (SPECL
          [`radii:((num#num)#num)list`;
           `center_gradient:
              (((num#num)#num)#((num#num)#num))list`;
           `hessian:
              ((((num#num)#num)#((num#num)#num))list)list`;
           `i - 1`]
          candle_q_dim_taylor_model_gradient_bounds_el) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "gradient_bound" THEN
    EXPAND_TAC "partial_error_q" THEN
    EXPAND_TAC "center_interval" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m_taylor_partial_error (f:real^N->real) i (lower,upper)
      (candle_q_list_real_vector radii)
      (candle_q_real partial_error_q)`
   (LABEL_TAC "partial_error") THENL
   [EXPAND_TAC "partial_error_q" THEN
    MATCH_MP_TAC candle_q_exact_hessian_m_taylor_partial_error THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval_arith (partial i (f:real^N->real) (y:real^N))
      (candle_q_real (FST center_interval),
       candle_q_real (SND center_interval))`
   (LABEL_TAC "center_partial_interval") THENL
   [EXPAND_TAC "center_interval" THEN
    MP_TAC
      (ASSUME
        `candle_q_interval_contains (EL (i - 1) center_gradient)
          (partial i (f:real^N->real) (y:real^N))`) THEN
    REWRITE_TAC[candle_q_interval_contains_def;
                Interval_arith.interval_arith];
    ALL_TAC] THEN
  let bounds_th =
      ISPECL
        [`((lower:real^N),(upper:real^N))`;
         `y:real^N`;
         `(candle_q_list_real_vector radii : real^N)`;
         `f:real^N->real`; `i:num`;
         `candle_q_real partial_error_q`;
         `candle_q_real (FST center_interval)`;
         `candle_q_real (SND center_interval)`;
         `candle_q_real (FST gradient_bound)`;
         `candle_q_real (SND gradient_bound)`]
        m_taylor_partial_bounds in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_cell_domain ((lower:real^N),(upper:real^N)) (y:real^N)
            (candle_q_list_real_vector radii)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME `diff2_domain ((lower:real^N),(upper:real^N))
          (f:real^N->real)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `m_taylor_partial_error (f:real^N->real) i (lower,upper)
            (candle_q_list_real_vector radii)
            (candle_q_real partial_error_q)`) in
  let bounds_th =
      MATCH_MP bounds_th
        (ASSUME
          `interval_arith (partial i (f:real^N->real) (y:real^N))
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
  let bounded_th =
    MATCH_MP (MATCH_MP bounds_th lower_th) upper_th in
  ONCE_REWRITE_TAC
    [ASSUME
      `EL (i - 1)
         (candle_q_dim_taylor_model_gradient_bounds
           radii center_gradient hessian) = gradient_bound`] THEN
  MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC (REWRITE_RULE[m_bounded_on_int] bounded_th) THEN
  DISCH_THEN (MP_TAC o SPEC `p:real^N`) THEN
  ASM_REWRITE_TAC[Interval_arith.interval_arith] THEN
  EXPAND_TAC "gradient_bound" THEN
  EXPAND_TAC "partial_error_q" THEN
  EXPAND_TAC "center_interval");;

let candle_q_exact_taylor_gradient_bounds_contains = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii center_gradient hessian (p:real^N).
     LENGTH radii = dimindex (:N) /\
     LENGTH center_gradient = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
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
     candle_q_stack_contains
       (candle_q_fixed_interval_list_round
         (candle_q_dim_taylor_model_gradient_bounds
           radii center_gradient hessian))
       (list_of_seq
         (\di. partial (di + 1) f p)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `(unrounded:
       (((num#num)#num)#((num#num)#num))list) =
      candle_q_dim_taylor_model_gradient_bounds
        radii center_gradient hessian` THEN
  SUBGOAL_THEN
   `LENGTH
      (unrounded:
        (((num#num)#num)#((num#num)#num))list) = dimindex (:N)`
   ASSUME_TAC THENL
   [EXPAND_TAC "unrounded" THEN
    MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `hessian:
            ((((num#num)#num)#((num#num)#num))list)list`]
        candle_q_dim_taylor_model_gradient_bounds_length) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_fixed_interval_list_round unrounded =
    list_of_seq
      (\di. EL di (candle_q_fixed_interval_list_round unrounded))
      (dimindex (:N))`
   (LABEL_TAC "rounded_gradient_sequence") THENL
   [MP_TAC
      (ISPECL
        [`dimindex (:N)`;
         `candle_q_fixed_interval_list_round unrounded`]
        candle_list_eq_list_of_seq_el) THEN
    ASM_REWRITE_TAC[candle_q_fixed_interval_list_round_length];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC
    [ASSUME
      `candle_q_fixed_interval_list_round unrounded =
       list_of_seq
         (\di. EL di (candle_q_fixed_interval_list_round unrounded))
         (dimindex (:N))`] THEN
  REWRITE_TAC[candle_q_stack_contains_all2;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `di + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `di < LENGTH (unrounded:
      (((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_fixed_interval_list_round_el] THEN
  EXPAND_TAC "unrounded" THEN
  MP_TAC
    (ISPECL
      [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
       `radii:((num#num)#num)list`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `hessian:
          ((((num#num)#num)#((num#num)#num))list)list`;
       `p:real^N`; `di + 1`]
      candle_q_exact_taylor_gradient_component_contains) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_exact_hessian_m_taylor_partial_error;
     candle_q_exact_taylor_gradient_component_contains;
     candle_q_exact_taylor_gradient_bounds_contains] then
  failwith "exact-rational Taylor gradient soundness: assumptions";;

print_endline
  "CANDLE_CV_EXACT_TAYLOR_GRADIENT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
