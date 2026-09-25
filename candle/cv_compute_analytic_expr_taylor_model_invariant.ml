(* ========================================================================== *)
(* Whole-box semantic invariant for the reflected centered Taylor checker.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The preceding checkpoint proves the scalar   *)
(* value and per-partial error contracts.  This layer assembles those facts  *)
(* into the whole gradient and complete analytic-jet invariant consumed by   *)
(* the paired-program soundness proof.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_semantics.ml";;

module Candle_cv_analytic_expr_taylor_model_invariant = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_partials;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_taylor_sound;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;

let candle_q_fixed_interval_list_round_el = prove
 (`!items i. i < LENGTH items
     ==> EL i (candle_q_fixed_interval_list_round items) =
         candle_q_fixed_interval_round (EL i items)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`items:(((num#num)#num)#((num#num)#num))list`; `i:num`]
      candle_q_fixed_interval_list_round_lookup) THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
               candle_q_fixed_interval_list_round_length]);;

let candle_q_dim_analytic_taylor_model_gradient_component_contains = prove
 (`!e boxes center_jet box_jet (p:real^N) i.
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
  let center_contains_th =
    REWRITE_RULE[GSYM center_list_th] center_contains_th in
  let center_regular_th =
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
   [MATCH_MP_TAC candle_q_dim_analytic_diff2_domain THEN
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
    MATCH_MP_TAC candle_q_dim_analytic_jet_complete_partial_error_sound THEN
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

let candle_list_eq_list_of_seq_el = prove
 (`!n (items:A list).
     LENGTH items = n
     ==> items = list_of_seq (\i. EL i items) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let candle_q_dim_analytic_taylor_model_gradient_contains = prove
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
        candle_q_dim_analytic_taylor_model_gradient_component_contains in
  let component_premises =
    end_itlist CONJ
        [ASSUME
          `candle_analytic_valid_dim (dimindex (:N)) e`;
         ASSUME `candle_q_dim_analytic_domain boxes e`;
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

let candle_q_dim_analytic_taylor_model_gradient_analytic_contains = prove
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
      candle_q_dim_analytic_taylor_model_gradient_contains in
  let partial_gradient_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME `candle_q_dim_analytic_domain boxes e`;
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
  let p_stack_th =
    MATCH_MP
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`; `p:real^N`]
        candle_q_box_stack_contains_vector)
      (CONJ
        (ASSUME
          `LENGTH
             (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)
        (ASSUME
          `(p:real^N) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) in
  let regular_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))`]
        candle_q_dim_analytic_domain_regular)
      (CONJ p_stack_th
        (ASSUME `candle_q_dim_analytic_domain boxes e`)) in
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

let candle_q_dim_jet_contains_components_of_stacks = prove
 (`!n jet (value:real) (gradient:num->real) (hessian:num->num->real).
     candle_q_dim_jet_shape n jet /\
     candle_q_interval_contains (candle_q_dim_jet_f jet) value /\
     candle_q_stack_contains
       (candle_q_dim_jet_gradient jet)
       (list_of_seq gradient n) /\
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian jet)
       (list_of_seq (\di. list_of_seq (hessian di) n) n)
     ==> candle_q_dim_jet_contains_components
           n jet value gradient hessian`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `di:num` THEN DISCH_TAC THEN
    REWRITE_TAC[candle_q_dim_jet_gradient_at_def] THEN
    SUBGOAL_THEN
     `candle_q_real_lookup di
        (list_of_seq (gradient:num->real) n) = gradient di`
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [ASM_SIMP_TAC[candle_q_real_lookup_list_of_seq];
      MATCH_MP_TAC candle_q_stack_lookup_contains THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`di:num`; `dj:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `candle_q_stack_contains
        (EL di (candle_q_dim_jet_hessian jet))
        (list_of_seq ((hessian:num->num->real) di) n)`
     (LABEL_TAC "hessian_row") THENL
     [ASM_MESON_TAC[candle_all2_right_list_of_seq_el];
      ALL_TAC] THEN
    REWRITE_TAC[candle_q_dim_jet_hessian_at_def] THEN
    SUBGOAL_THEN
     `candle_q_dim_interval_row_lookup di
        (candle_q_dim_jet_hessian jet) =
      EL di (candle_q_dim_jet_hessian jet)`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN
       `di < LENGTH (candle_q_dim_jet_hessian jet)`
       ASSUME_TAC THENL
       [MP_TAC
          (REWRITE_RULE[candle_q_dim_jet_shape_def;
                        candle_q_dim_interval_matrix_shape_def]
            (ASSUME `candle_q_dim_jet_shape n jet`)) THEN
        ASM_MESON_TAC[];
        ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_real_lookup dj
        (list_of_seq ((hessian:num->num->real) di) n) = hessian di dj`
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [ASM_SIMP_TAC[candle_q_real_lookup_list_of_seq];
      ASM_MESON_TAC[candle_q_stack_lookup_contains]]]);;

let candle_q_dim_analytic_taylor_model_box_proxy_def = new_definition
 `candle_q_dim_analytic_taylor_model_box_proxy boxes center_jet box_jet =
    candle_q_dim_taylor_model_proxy
      (candle_q_dim_taylor_model_result_complete
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        T center_jet (candle_q_dim_jet_hessian box_jet))`;;

let candle_q_dim_analytic_taylor_model_proxy_contains = prove
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
    ASM_MESON_TAC[candle_q_dim_analytic_taylor_model_value_bound_contains];
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
      candle_q_dim_analytic_taylor_model_gradient_analytic_contains in
  let gradient_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME `candle_q_dim_analytic_domain boxes e`;
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

end;;
