(* ========================================================================== *)
(* Universal analytic-invariant bridge for the fixed algebraic conversion.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant = struct

open Multivariate_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_partials;;
open Candle_cv_analytic_expr_hessian;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;

(* This file constructs fully instantiated theorems before closing their    *)
(* corresponding goals.  Reapplying an older matcher                       *)
(* instantiation with [ACCEPT_TAC] can attempt an invalid abstraction under *)
(* the theorem's quantified hypotheses.  The kernel theorem already has    *)
(* exactly the current conclusion, so no further instantiation is needed.   *)
let candle_fsa_accept_instantiated (th:thm) : tactic =
  fun (_,goal) ->
    if aconv (concl th) goal then
      null_meta,[],(fun _ [] -> th)
    else failwith "candle_fsa_accept_instantiated";;

let candle_fsa_label_instantiated label (th:thm) : tactic =
  fun (assumptions,goal) ->
    null_meta,[((label,th)::assumptions,goal)],
      (fun _ [result] -> PROVE_HYP th result);;

let candle_fsa_result_of_q_analytic_invariant = prove
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
       (candle_fs_result_to_q (candle_fsa_result_of_q result))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fsa_result_of_q_domain_roundtrip] THEN
  DISCH_TAC THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  POP_ASSUM
   (fun box_contains_th ->
      POP_ASSUM
       (fun proxy_shape_th ->
          LABEL_TAC "box_contains_all" box_contains_th THEN
          LABEL_TAC "proxy_shape" proxy_shape_th)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fsa_result_of_q_center] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_shape THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "proxy_shape" MP_TAC THEN
      REWRITE_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_taylor_model_proxy_hessian] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[candle_fsa_result_of_q_center] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_contains_components THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      MP_TAC
       (MATCH_MP
         (ISPECL
           [`dimindex (:N)`;
            `candle_q_dim_taylor_model_proxy
              (result:
                bool#
                ((((num#num)#num)#(num#num)#num)#
                 (((num#num)#num)#(num#num)#num)list#
                 ((((num#num)#num)#(num#num)#num)list)list)#
                (((num#num)#num)#(num#num)#num)#
                (((num#num)#num)#(num#num)#num)list#
                ((((num#num)#num)#(num#num)#num)list)list)`;
            `list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))`;
            `center_e:candle_analytic_expr`;
            `box_e:candle_analytic_expr`]
           candle_q_dim_analytic_contains_certificate_transport)
         (ASSUME
           `candle_analytic_erase_sqrt_certificates center_e =
            candle_analytic_erase_sqrt_certificates box_e`)) THEN
      DISCH_THEN (fun th -> MATCH_MP_TAC (snd (EQ_IMP_RULE th))) THEN
      USE_THEN "box_contains_all"
       (fun th ->
          MATCH_MP_TAC
           (SPEC `(candle_q_box_center_vector boxes : real^N)` th)) THEN
      MATCH_MP_TAC y_in_domain THEN
      EXISTS_TAC `(candle_q_box_radius_vector boxes : real^N)` THEN
      MATCH_MP_TAC candle_q_box_m_cell_domain THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[candle_fsa_result_of_q_proxy] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_shape THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "proxy_shape" MP_TAC THEN
      REWRITE_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_taylor_model_proxy_hessian] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[candle_fsa_result_of_q_proxy] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_contains_components THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      USE_THEN "box_contains_all"
       (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      USE_THEN "box_contains_all"
       (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_dim_flyspeck_components_analytic_contains = prove
 (`!e jet (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e /\
     candle_q_dim_jet_contains_components (dimindex (:N)) jet
       (candle_analytic_denote_dim e z)
       (\di. partial (di + 1) (candle_analytic_denote_dim e) z)
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_analytic_denote_dim e) z)
     ==>
     candle_q_dim_analytic_contains (dimindex (:N)) jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM candle_analytic_denote_dim_def] THEN
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `di:num` THEN DISCH_TAC THEN
    MP_TAC
      (SPECL
        [`e:candle_analytic_expr`; `z:real^N`; `di + 1`]
        candle_analytic_denote_dim_partial) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      DISCH_THEN
       (fun th ->
          ONCE_REWRITE_TAC
           [GSYM
             (REWRITE_RULE
               [ARITH_RULE `(di + 1) - 1 = di`] th)]) THEN
      FIRST_ASSUM
        (fun th -> MATCH_MP_TAC (SPEC `di:num` th)) THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`di:num`; `dj:num`] THEN STRIP_TAC THEN
    MP_TAC
      (SPECL
        [`e:candle_analytic_expr`; `z:real^N`; `di + 1`; `dj + 1`]
        candle_analytic_denote_dim_second_partial) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      DISCH_THEN
       (fun th ->
          ONCE_REWRITE_TAC
           [GSYM
             (REWRITE_RULE
               [ARITH_RULE `(di + 1) - 1 = di`;
                ARITH_RULE `(dj + 1) - 1 = dj`] th)]) THEN
      FIRST_ASSUM
        (fun th -> MATCH_MP_TAC (SPECL [`di:num`; `dj:num`] th)) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_analytic_dd_matrix_flyspeck = prove
 (`!e (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     list_of_seq
       (\di. list_of_seq
         (\dj. candle_analytic_dd di dj
           (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
         (dimindex (:N)))
       (dimindex (:N)) =
     list_of_seq
       (\di. list_of_seq
         (\dj. partial2 (dj + 1) (di + 1)
           (candle_analytic_denote_dim e) z)
         (dimindex (:N)))
       (dimindex (:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `dj:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC
    (SPECL
      [`e:candle_analytic_expr`; `z:real^N`; `di + 1`; `dj + 1`]
      candle_analytic_denote_dim_second_partial) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN
     (fun th ->
        MATCH_ACCEPT_TAC
          (SYM
            (REWRITE_RULE
              [ARITH_RULE `(di + 1) - 1 = di`;
               ARITH_RULE `(dj + 1) - 1 = dj`] th)))]);;

let candle_fs_result_complete_proxy_contains_box = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii center hessian (domain_ok:bool) (p:real^N).
     LENGTH radii = dimindex (:N) /\
     LENGTH (candle_fs_first_gradient center) = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\row. LENGTH row = dimindex (:N)) hessian /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain (lower,upper) y (candle_fs_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_fs_interval_contains (candle_fs_first_value center) (f y) /\
     ALL2 candle_fs_interval_contains (candle_fs_first_gradient center)
       (list_of_seq (\di. partial (di + 1) f y) (dimindex (:N))) /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q
           (candle_fs_result_complete_rounded
             radii domain_ok center hessian)))
       (f p)
       (\di. partial (di + 1) f p)
       (\di dj. partial2 (dj + 1) (di + 1) f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_result_complete_proxy_contains THEN
  MAP_EVERY EXISTS_TAC
    [`((lower:real^N),(upper:real^N))`; `y:real^N`] THEN
  ASM_REWRITE_TAC[FST; SND]);;

let candle_fs_result_complete_proxy_analytic_contains_box = prove
 (`!e (lower:real^N) (upper:real^N) (y:real^N)
       radii center hessian (domain_ok:bool).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(p:real^N). p IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e) /\
     LENGTH radii = dimindex (:N) /\
     LENGTH (candle_fs_first_gradient center) = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\row. LENGTH row = dimindex (:N)) hessian /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain (lower,upper) y (candle_fs_list_real_vector radii) /\
     diff2_domain (lower,upper) (candle_analytic_denote_dim e) /\
     candle_fs_interval_contains (candle_fs_first_value center)
       (candle_analytic_denote_dim e y) /\
     ALL2 candle_fs_interval_contains (candle_fs_first_gradient center)
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) y)
         (dimindex (:N))) /\
     (!(p:real^N). p IN interval [lower,upper]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1)
                   (candle_analytic_denote_dim e) p)
                 (dimindex (:N)))
               (dimindex (:N))))
     ==>
     !(p:real^N). p IN interval [lower,upper]
       ==> candle_q_dim_analytic_contains (dimindex (:N))
             (candle_q_dim_taylor_model_proxy
               (candle_fs_result_to_q
                 (candle_fs_result_complete_rounded
                   radii domain_ok center hessian)))
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_q_dim_flyspeck_components_analytic_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_result_complete_proxy_contains_box THEN
    MAP_EVERY EXISTS_TAC
      [`(lower:real^N)`; `(upper:real^N)`; `(y:real^N)`] THEN
    ASM_REWRITE_TAC[]]);;

(* Complete a fixed-scale first jet and whole-box Hessian without falling   *)
(* back to per-component theorem construction.  This is the analytic form   *)
(* of [candle_fs_result_complete_poly_invariant]: it connects the generic    *)
(* source semantics to the same fixed arithmetic completion used by the hot *)
(* evaluator.                                                               *)

let candle_fs_result_complete_analytic_invariant = prove
 (`!center_e box_e boxes domain center hessian (type_witness:real^N).
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
       candle_q_dim_jet_shape (dimindex (:N))
         (candle_fs_first_to_q center hessian) /\
       candle_q_dim_analytic_contains (dimindex (:N))
         (candle_fs_first_to_q center hessian)
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       (!(p:real^N). p IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
                (list_of_seq
                  (\di. list_of_seq
                    (\dj. partial2 (dj + 1) (di + 1)
                      (candle_analytic_denote_dim box_e) p)
                    (dimindex (:N)))
                  (dimindex (:N)))))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       (candle_fs_result_to_q
         (candle_fs_result_complete_rounded
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           domain center hessian))
       center_e box_e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (fun all_premises_th ->
      let valid_th,rest1 = CONJ_PAIR all_premises_th in
      let erasure_th,rest2 = CONJ_PAIR rest1 in
      let length_th,rest3 = CONJ_PAIR rest2 in
      let boxes_valid_th,complete_premises_th = CONJ_PAIR rest3 in
      EVERY
       [candle_fsa_label_instantiated "valid" valid_th;
        candle_fsa_label_instantiated "erasure" erasure_th;
        candle_fsa_label_instantiated "boxes_length" length_th;
        candle_fsa_label_instantiated "boxes_valid" boxes_valid_th;
        candle_fsa_label_instantiated "complete_premises"
          complete_premises_th]) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_result_to_q_domain;
              candle_fs_result_complete_domain] THEN
  DISCH_THEN (candle_fsa_label_instantiated "domain") THEN
  USE_THEN "complete_premises"
   (fun complete_premises_th ->
      USE_THEN "domain"
       (fun domain_th ->
          let enabled_th = MATCH_MP complete_premises_th domain_th in
          let center_regular_th,rest1 = CONJ_PAIR enabled_th in
          let box_regular_th,rest2 = CONJ_PAIR rest1 in
          let center_shape_th,rest3 = CONJ_PAIR rest2 in
          let center_contains_th,hessian_contains_th = CONJ_PAIR rest3 in
          EVERY
           [candle_fsa_label_instantiated "center_regular"
              center_regular_th;
            candle_fsa_label_instantiated "box_regular_all"
              box_regular_th;
            candle_fsa_label_instantiated "center_shape" center_shape_th;
            candle_fsa_label_instantiated "center_contains"
              center_contains_th;
            candle_fsa_label_instantiated "hessian_contains_all"
              hessian_contains_th])) THEN
  SUBGOAL_THEN
   `candle_analytic_regular_at
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) box_e`
   (LABEL_TAC "center_regular_box") THENL
   [MATCH_MP_TAC
      (fst
        (EQ_IMP_RULE
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
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N))
      (candle_fs_first_to_q center hessian)
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) box_e`
   (LABEL_TAC "center_contains_box") THENL
   [MATCH_MP_TAC
      (fst
        (EQ_IMP_RULE
          (MATCH_MP
            (ISPECL
              [`dimindex (:N)`;
               `candle_fs_first_to_q center hessian`;
               `list_of_seq
                 (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
                 (dimindex (:N))`;
               `center_e:candle_analytic_expr`;
               `box_e:candle_analytic_expr`]
              candle_q_dim_analytic_contains_certificate_transport)
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_analytic_valid_dim (dimindex (:N)) box_e /\
    (!(p:real^N). p IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e) /\
    LENGTH
      (candle_fs_list_of_q
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))) =
      dimindex (:N) /\
    LENGTH (candle_fs_first_gradient center) = dimindex (:N) /\
    LENGTH hessian = dimindex (:N) /\
    ALL (\row. LENGTH row = dimindex (:N)) hessian /\
    ALL (\r. &0 <= candle_fs_real r)
      (candle_fs_list_of_q
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))) /\
    m_cell_domain
      ((candle_q_box_lower_vector boxes : real^N),
       (candle_q_box_upper_vector boxes : real^N))
      (candle_q_box_center_vector boxes : real^N)
      (candle_fs_list_real_vector
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper
            (candle_q_radius_list boxes)))) /\
    diff2_domain
      ((candle_q_box_lower_vector boxes : real^N),
       (candle_q_box_upper_vector boxes : real^N))
      (candle_analytic_denote_dim box_e) /\
    candle_fs_interval_contains (candle_fs_first_value center)
      (candle_analytic_denote_dim box_e
        (candle_q_box_center_vector boxes : real^N)) /\
    ALL2 candle_fs_interval_contains (candle_fs_first_gradient center)
      (list_of_seq
        (\di. partial (di + 1) (candle_analytic_denote_dim box_e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))) /\
    (!(p:real^N). p IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1)
                   (candle_analytic_denote_dim box_e) p)
                 (dimindex (:N)))
               (dimindex (:N))))`
   (FREEZE_THEN (LABEL_TAC "proxy_analytic_premises")) THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "box_regular_all" ACCEPT_TAC;
      ASM_REWRITE_TAC[candle_fs_list_of_q_length;
                      candle_q_fixed_list_round_upper_length;
                      candle_q_radius_list_length];
      USE_THEN "center_shape" MP_TAC THEN
      REWRITE_TAC[candle_fs_first_to_q_shape] THEN MESON_TAC[];
      USE_THEN "center_shape" MP_TAC THEN
      REWRITE_TAC[candle_fs_first_to_q_shape] THEN MESON_TAC[];
      USE_THEN "center_shape" MP_TAC THEN
      REWRITE_TAC[candle_fs_first_to_q_shape] THEN MESON_TAC[];
      ASM_MESON_TAC[candle_fs_rounded_list_nonnegative;
                    candle_q_fixed_list_round_upper_nonnegative;
                    candle_q_radius_list_nonnegative];
      ASM_MESON_TAC[candle_fs_rounded_radii_m_cell_domain];
      MATCH_MP_TAC candle_q_dim_analytic_regular_diff2_domain THEN
      ASM_REWRITE_TAC[];
      USE_THEN "center_contains_box" MP_TAC THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_q_dim_jet_contains_components_def;
                  candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                  candle_fs_interval_to_q_contains; FST; SND;
                  candle_analytic_denote_dim_def] THEN
      MESON_TAC[];
      MP_TAC
        (ISPECL
          [`box_e:candle_analytic_expr`;
           `candle_fs_first_to_q center hessian`;
           `(candle_q_box_center_vector boxes : real^N)`]
          candle_q_dim_analytic_jet_gradient_flyspeck_contains) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
                  candle_fs_interval_list_to_q_contains; FST; SND];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_fs_result_complete_center];
    ASM_REWRITE_TAC[candle_fs_result_complete_center];
    MATCH_MP_TAC candle_fs_result_complete_proxy_shape THEN
    ASM_REWRITE_TAC[];
    USE_THEN "proxy_analytic_premises"
      (fun premises_th ->
         let all_points_th =
           MATCH_MP
             (ISPECL
               [`box_e:candle_analytic_expr`;
                `(candle_q_box_lower_vector boxes : real^N)`;
                `(candle_q_box_upper_vector boxes : real^N)`;
                `(candle_q_box_center_vector boxes : real^N)`;
                `candle_fs_list_of_q
                  (candle_q_fixed_list_round_upper
                    (candle_q_radius_list boxes))`;
                `center:((num#num)#(num#num))#
                  (((num#num)#(num#num))list)`;
                `hessian:(((num#num)#(num#num))list)list`;
                `domain:bool`]
               candle_fs_result_complete_proxy_analytic_contains_box)
             premises_th in
         candle_fsa_accept_instantiated all_points_th)]);;

(* Operation closure consumes the universal invariant through the fixed-data *)
(* center and Hessian views below.  Keeping these projections generic avoids *)
(* redoing analytic differentiation for every postfix constructor.           *)

let candle_fs_result_analytic_center_shape = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center result)
         (candle_fs_result_hessian result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_analytic_center_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) center_e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_analytic_center_value_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_fs_interval_contains
       (candle_fs_first_value (candle_fs_result_center result))
       (candle_analytic_value
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_center_contains) THEN
  ASM_REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_q_dim_jet_contains_components_def;
                  candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                  candle_fs_interval_to_q_contains; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_analytic_center_gradient_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient (candle_fs_result_center result))
       (list_of_seq
         (\di. candle_analytic_d di
           (list_of_seq
             (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
             (dimindex (:N))) center_e)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_center_shape)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes
         (candle_fs_result_to_q result) center_e box_e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let contains_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_center_contains)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes
         (candle_fs_result_to_q result) center_e box_e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th =
    REWRITE_RULE[candle_q_dim_analytic_contains_def] contains_th in
  let center_jet = rand (concl shape_th) in
  let gradient_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`; center_jet;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e`;
      `(\di. candle_analytic_d di
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->num->real`]
     candle_q_dim_jet_components_gradient_contains)
   (CONJ shape_th components_th) in
  candle_fsa_accept_instantiated
   (REWRITE_RULE
     [candle_fs_first_to_q_def;
      candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
      candle_fs_interval_list_to_q_contains; FST; SND]
     gradient_th));;

let candle_fs_result_analytic_center_hessian_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian result)
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq
               (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
               (dimindex (:N))) center_e)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_center_shape)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes
         (candle_fs_result_to_q result) center_e box_e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let contains_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_center_contains)
   (CONJ
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes
         (candle_fs_result_to_q result) center_e box_e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th =
    REWRITE_RULE[candle_q_dim_analytic_contains_def] contains_th in
  let center_jet = rand (concl shape_th) in
  let hessian_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`; center_jet;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e`;
      `(\di. candle_analytic_d di
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->num->real`]
     candle_q_dim_jet_components_hessian_contains)
   (CONJ shape_th components_th) in
  candle_fsa_accept_instantiated
   (REWRITE_RULE
     [candle_fs_first_to_q_def;
      candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
      candle_fs_interval_matrix_to_q_contains; FST; SND]
     hessian_th));;

let candle_fs_result_analytic_proxy_shape = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_result_to_q_domain] THEN
  MESON_TAC[]);;

let candle_fs_result_analytic_proxy_data_shape = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     LENGTH (candle_fs_result_gradient_bounds result) = dimindex (:N) /\
     LENGTH (candle_fs_result_hessian result) = dimindex (:N) /\
     ALL (\row. LENGTH row = dimindex (:N))
       (candle_fs_result_hessian result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`center_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_shape) THEN
  ASM_REWRITE_TAC[candle_fs_result_proxy_to_q_shape]);;

let candle_fs_result_analytic_box_regular = prove
 (`!center_e box_e boxes result (type_witness:real^N) (p:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_analytic_regular_at
       (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_result_to_q_domain] THEN
  MESON_TAC[]);;

let candle_fs_result_analytic_box_hessian_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian result)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim box_e) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let invariant_th =
    REWRITE_RULE
     [candle_q_dim_taylor_model_result_analytic_invariant_def;
      candle_fs_result_to_q_def;
      candle_q_dim_taylor_model_result_domain_def;
      candle_q_dim_taylor_model_result_make_def; FST; SND]
     (ASSUME
       `candle_q_dim_taylor_model_result_analytic_invariant
         (type_witness:real^N) boxes
         (candle_fs_result_to_q result) center_e box_e`) in
  let enabled_th = MATCH_MP invariant_th
    (ASSUME
      `candle_fs_result_domain
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`) in
  let _,rest1 = CONJ_PAIR enabled_th in
  let box_regular_all_th,rest2 = CONJ_PAIR rest1 in
  let _,rest3 = CONJ_PAIR rest2 in
  let _,rest4 = CONJ_PAIR rest3 in
  let proxy_shape_th,box_contains_all_th = CONJ_PAIR rest4 in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let regular_th = MATCH_MP (SPEC `p:real^N` box_regular_all_th)
    point_th in
  let contains_th = MATCH_MP (SPEC `p:real^N` box_contains_all_th)
    point_th in
  let bridge_rule = REWRITE_RULE
    [candle_fs_result_to_q_def;
     candle_q_dim_taylor_model_result_make_def; FST; SND]
    (ISPECL
      [`box_e:candle_analytic_expr`;
       `candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
       `p:real^N`]
      candle_q_dim_analytic_jet_hessian_flyspeck_contains) in
  let bridge_premises = CONJ
      (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_e`)
      (CONJ regular_th (CONJ proxy_shape_th contains_th)) in
  let bridge_th = MATCH_MP bridge_rule bridge_premises in
  let final_th = REWRITE_RULE
    [candle_q_dim_taylor_model_proxy_def;
     candle_fs_result_to_q_def;
     candle_q_dim_taylor_model_result_hessian_def;
     candle_q_dim_taylor_model_result_make_def;
     candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
     candle_fs_interval_matrix_to_q_contains; FST; SND]
    bridge_th in
  candle_fsa_accept_instantiated final_th);;

(* Fixed negation is exact at the selected scale.  The completed value and *)
(* gradient are the normalized negation of the source center, while the     *)
(* whole-box Hessian remains fixed data and is exposed through its exact     *)
(* rational view for the universal analytic bridge.                          *)

let candle_fs_result_neg_analytic_invariant = prove
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
         (candle_fs_result_neg
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           result))
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_fs_result_neg_def] THEN
  ASM_CASES_TAC
   `candle_fs_result_domain
     (result:
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
      USE_THEN "input_invariant"
       (fun input_invariant_th ->
          let enabled_th = MATCH_MP
            (REWRITE_RULE
              [candle_q_dim_taylor_model_result_analytic_invariant_def;
               candle_fs_result_to_q_domain]
              input_invariant_th)
            (ASSUME
              `candle_fs_result_domain
                (result:
                  bool#
                  (((num#num)#(num#num))#
                    ((num#num)#(num#num))list)#
                  ((num#num)#(num#num))#
                  ((num#num)#(num#num))list#
                  (((num#num)#(num#num))list)list)`) in
          let center_regular_th,rest1 = CONJ_PAIR enabled_th in
          let box_regular_all_th,rest2 = CONJ_PAIR rest1 in
          let center_shape_th,rest3 = CONJ_PAIR rest2 in
          let center_contains_th,rest4 = CONJ_PAIR rest3 in
          let proxy_shape_th,box_contains_all_th = CONJ_PAIR rest4 in
          EVERY
           [candle_fsa_label_instantiated "center_regular"
              center_regular_th;
            candle_fsa_label_instantiated "box_regular_all"
              box_regular_all_th;
            candle_fsa_label_instantiated "center_shape"
              center_shape_th;
            candle_fsa_label_instantiated "center_contains"
              center_contains_th;
            candle_fsa_label_instantiated "proxy_shape" proxy_shape_th;
            candle_fsa_label_instantiated "box_contains_all"
              box_contains_all_th]) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "center_regular" MP_TAC THEN
        REWRITE_TAC[candle_analytic_regular_at_def];
        USE_THEN "box_regular_all" MP_TAC THEN
        REWRITE_TAC[candle_analytic_regular_at_def];
        REWRITE_TAC[candle_fs_first_to_q_neg] THEN
        MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
        USE_THEN "center_shape" MP_TAC THEN
        REWRITE_TAC[candle_fs_result_to_q_def;
                    candle_q_dim_taylor_model_result_center_def;
                    candle_q_dim_taylor_model_result_make_def; FST; SND];
        REWRITE_TAC[candle_fs_first_to_q_neg;
                    candle_q_dim_analytic_contains_def;
                    candle_analytic_value_def;
                    candle_analytic_d_def;
                    candle_analytic_dd_def] THEN
        MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
        CONJ_TAC THENL
         [USE_THEN "center_shape" MP_TAC THEN
          REWRITE_TAC[candle_fs_result_to_q_def;
                      candle_q_dim_taylor_model_result_center_def;
                      candle_q_dim_taylor_model_result_make_def; FST; SND];
          REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
          USE_THEN "center_contains" MP_TAC THEN
          REWRITE_TAC[candle_fs_result_to_q_def;
                      candle_q_dim_taylor_model_result_center_def;
                      candle_q_dim_taylor_model_result_make_def; FST; SND]];
        X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC[GSYM candle_fs_interval_matrix_to_q_contains] THEN
        REWRITE_TAC[candle_fs_interval_matrix_to_q_neg] THEN
        ONCE_REWRITE_TAC
          [GSYM
            (REWRITE_RULE
              [candle_q_dim_taylor_model_result_hessian_def;
               candle_fs_result_to_q_def;
               candle_q_dim_taylor_model_result_make_def; FST; SND]
              (ISPEC
                `candle_fs_result_to_q
                  (result:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list)`
                candle_q_dim_taylor_model_proxy_neg_hessian))] THEN
        let hessian_rule =
          REWRITE_RULE
           [candle_fs_result_to_q_def;
            candle_q_dim_taylor_model_result_make_def; FST; SND]
           (ISPECL
             [`Candle_analytic_neg box_e`;
              `candle_q_dim_jet_normalized_neg
                (candle_q_dim_taylor_model_proxy
                  (candle_fs_result_to_q
                    (result:
                      bool#
                      (((num#num)#(num#num))#
                        ((num#num)#(num#num))list)#
                      ((num#num)#(num#num))#
                      ((num#num)#(num#num))list#
                      (((num#num)#(num#num))list)list)))`;
              `p:real^N`]
             candle_q_dim_analytic_jet_hessian_flyspeck_contains) in
        SUBGOAL_THEN
         `candle_analytic_valid_dim (dimindex (:N))
            (Candle_analytic_neg box_e) /\
          candle_analytic_regular_at
            (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
            (Candle_analytic_neg box_e) /\
          candle_q_dim_jet_shape (dimindex (:N))
            (candle_q_dim_jet_normalized_neg
              (candle_q_dim_taylor_model_proxy
                (candle_fs_result_to_q
                  (result:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list)))) /\
          candle_q_dim_analytic_contains (dimindex (:N))
            (candle_q_dim_jet_normalized_neg
              (candle_q_dim_taylor_model_proxy
                (candle_fs_result_to_q
                  (result:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list))))
            (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
            (Candle_analytic_neg box_e)`
         (fun premises_th ->
            let normalized_premises_th =
              REWRITE_RULE
               [candle_fs_result_to_q_def;
                candle_q_dim_taylor_model_result_make_def; FST; SND]
               premises_th in
            candle_fsa_accept_instantiated
              (MATCH_MP hessian_rule normalized_premises_th)) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
          REWRITE_TAC[candle_analytic_regular_at_def] THEN
          USE_THEN "box_regular_all"
           (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
          USE_THEN "proxy_shape" MP_TAC THEN
          REWRITE_TAC[candle_fs_result_to_q_def;
                      candle_q_dim_taylor_model_result_make_def; FST; SND];
          REWRITE_TAC[candle_q_dim_analytic_contains_def;
                      candle_analytic_value_def;
                      candle_analytic_d_def;
                      candle_analytic_dd_def] THEN
          MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
          CONJ_TAC THENL
           [USE_THEN "proxy_shape" MP_TAC THEN
            REWRITE_TAC[candle_fs_result_to_q_def;
                        candle_q_dim_taylor_model_result_make_def;
                        FST; SND];
            REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
            USE_THEN "box_contains_all"
             (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
            ASM_REWRITE_TAC[]]]]];
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
                candle_fs_result_to_q_domain;
                candle_fs_result_complete_domain] THEN
    ASM_REWRITE_TAC[]]);;

(* Fixed addition combines the source center enclosures pointwise.  This is *)
(* the analytic counterpart of the polynomial center closure, stated only   *)
(* in terms of the universal value/gradient/Hessian semantics.               *)

let candle_fs_result_add_center_analytic_contains = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q left) center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q right) center_b box_b /\
     candle_fs_result_domain left /\
     candle_fs_result_domain right
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_first_make
           (candle_fs_interval_add
             (candle_fs_first_value (candle_fs_result_center left))
             (candle_fs_first_value (candle_fs_result_center right)))
           (candle_fs_interval_list_add
             (candle_fs_first_gradient (candle_fs_result_center left))
             (candle_fs_first_gradient (candle_fs_result_center right))))
         (candle_fs_interval_matrix_add
           (candle_fs_result_hessian left)
           (candle_fs_result_hessian right)))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
       (Candle_analytic_add center_a center_b)`,
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
  let left_shape_th = MATCH_MP
    (left_instance candle_fs_result_analytic_center_shape)
    left_premises_th in
  let right_shape_th = MATCH_MP
    (right_instance candle_fs_result_analytic_center_shape)
    right_premises_th in
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
  let left_hessian_th = MATCH_MP
    (left_instance candle_fs_result_analytic_center_hessian_contains)
    left_premises_th in
  let right_hessian_th = MATCH_MP
    (right_instance candle_fs_result_analytic_center_hessian_contains)
    right_premises_th in
  let add_th = MATCH_MP candle_fs_first_add_components
    (CONJ left_shape_th
      (CONJ right_shape_th
        (CONJ left_value_th
          (CONJ right_value_th
            (CONJ left_gradient_th
              (CONJ right_gradient_th
                (CONJ left_hessian_th right_hessian_th))))))) in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  candle_fsa_accept_instantiated
    (CONV_RULE (DEPTH_CONV BETA_CONV) add_th));;

let candle_fs_result_add_box_hessian_contains = prove
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
       (candle_fs_interval_matrix_add
         (candle_fs_result_hessian left)
         (candle_fs_result_hessian right))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim
               (Candle_analytic_add box_a box_b)) p)
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
  let left_hessian_th = MATCH_MP
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
     candle_fs_result_analytic_box_hessian_contains)
   (CONJ
     (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_a`)
     (CONJ left_invariant_th (CONJ left_domain_th point_th))) in
  let right_hessian_th = MATCH_MP
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
     candle_fs_result_analytic_box_hessian_contains)
   (CONJ
     (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_b`)
     (CONJ right_invariant_th (CONJ right_domain_th point_th))) in
  let left_data_th = MATCH_MP
   (ISPECL
     [`center_a:candle_analytic_expr`; `box_a:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `left:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ left_invariant_th left_domain_th) in
  let right_data_th = MATCH_MP
   (ISPECL
     [`center_b:candle_analytic_expr`; `box_b:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `right:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ right_invariant_th right_domain_th) in
  let _,left_matrix_shape_th = CONJ_PAIR left_data_th in
  let left_length_th,left_rows_th = CONJ_PAIR left_matrix_shape_th in
  let _,right_matrix_shape_th = CONJ_PAIR right_data_th in
  let right_length_th,right_rows_th = CONJ_PAIR right_matrix_shape_th in
  let left_values =
   `list_of_seq
      (\di. list_of_seq
        (\dj. partial2 (dj + 1) (di + 1)
          (candle_analytic_denote_dim box_a) (p:real^N))
        (dimindex (:N)))
      (dimindex (:N))` in
  let right_values =
   `list_of_seq
      (\di. list_of_seq
        (\dj. partial2 (dj + 1) (di + 1)
          (candle_analytic_denote_dim box_b) (p:real^N))
        (dimindex (:N)))
      (dimindex (:N))` in
  let add_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_hessian
        (left:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      left_values;
      `candle_fs_result_hessian
        (right:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      right_values]
     candle_fs_interval_matrix_add_contains)
   (CONJ
     (TRANS left_length_th (SYM right_length_th))
     (CONJ left_rows_th
       (CONJ right_rows_th
         (CONJ left_hessian_th right_hessian_th)))) in
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
  let left_diff2_th = MATCH_MP diff2c_imp_diff2
   (MATCH_MP
     (SPECL [`box_a:candle_analytic_expr`; `p:real^N`]
       candle_analytic_denote_dim_diff2c)
     (CONJ
       (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_a`)
       left_regular_th)) in
  let right_diff2_th = MATCH_MP diff2c_imp_diff2
   (MATCH_MP
     (SPECL [`box_b:candle_analytic_expr`; `p:real^N`]
       candle_analytic_denote_dim_diff2c)
     (CONJ
       (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_b`)
       right_regular_th)) in
  let di = `di:num` and dj = `dj:num` in
  let partial_add_th = GEN di (GEN dj
   (MP
     (MP
       (SPECL
         [`p:real^N`; `dj + 1`; `di + 1`;
          `(candle_analytic_denote_dim box_a):real^N->real`;
          `(candle_analytic_denote_dim box_b):real^N->real`]
         second_partial_add)
       left_diff2_th)
     right_diff2_th)) in
  ASSUME_TAC left_diff2_th THEN ASSUME_TAC right_diff2_th THEN
  MP_TAC add_th THEN
  ASM_SIMP_TAC[candle_map2_matrix_list_of_seq;
               candle_analytic_denote_dim_add; partial_add_th]);;

let candle_fs_result_add_analytic_invariant = prove
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
         (candle_fs_result_add
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           left right))
       (Candle_analytic_add center_a center_b)
       (Candle_analytic_add box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
   (fun right_th ->
      POP_ASSUM
       (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_fs_result_add_def] THEN
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
              let left_shape_th = MATCH_MP
               (ISPECL
                 [`center_a:candle_analytic_expr`;
                  `box_a:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `left:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `type_witness:real^N`]
                 candle_fs_result_analytic_center_shape)
               (CONJ left_invariant_th left_domain_th) in
              let right_shape_th = MATCH_MP
               (ISPECL
                 [`center_b:candle_analytic_expr`;
                  `box_b:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `right:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list`;
                  `type_witness:real^N`]
                 candle_fs_result_analytic_center_shape)
               (CONJ right_invariant_th right_domain_th) in
              let add_shape_th = MATCH_MP candle_fs_first_add_shape
                (CONJ left_shape_th right_shape_th) in
              let add_center_th = MATCH_MP
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
                 candle_fs_result_add_center_analytic_contains)
               (CONJ left_invariant_th
                 (CONJ right_invariant_th
                   (CONJ left_domain_th right_domain_th))) in
              let p = `p:real^N` in
              let point_property =
               `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]` in
              let add_box_point_th = MATCH_MP
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
                 candle_fs_result_add_box_hessian_contains)
               (CONJ
                 (ASSUME
                   `candle_analytic_valid_dim (dimindex (:N)) box_a`)
                 (CONJ
                   (ASSUME
                     `candle_analytic_valid_dim (dimindex (:N)) box_b`)
                   (CONJ left_invariant_th
                     (CONJ right_invariant_th
                       (CONJ left_domain_th
                         (CONJ right_domain_th
                           (ASSUME point_property))))))) in
              let add_box_all_th = GEN p
                (DISCH point_property add_box_point_th) in
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
                  "add_center_shape" add_shape_th;
                candle_fsa_label_instantiated
                  "add_center_contains" add_center_th;
                candle_fsa_label_instantiated
                  "add_box_hessian_all" add_box_all_th])) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[candle_analytic_regular_at_def] THEN CONJ_TAC THENL
         [USE_THEN "left_center_regular" ACCEPT_TAC;
          USE_THEN "right_center_regular" ACCEPT_TAC];
        X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        REWRITE_TAC[candle_analytic_regular_at_def] THEN CONJ_TAC THENL
         [USE_THEN "left_box_regular"
           (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
          ASM_REWRITE_TAC[];
          USE_THEN "right_box_regular"
           (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
          ASM_REWRITE_TAC[]];
        USE_THEN "add_center_shape"
          candle_fsa_accept_instantiated;
        USE_THEN "add_center_contains"
          candle_fsa_accept_instantiated;
        X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        USE_THEN "add_box_hessian_all"
         (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
                candle_fs_result_to_q_domain;
                candle_fs_result_complete_domain] THEN
    ASM_REWRITE_TAC[]]);;

end;;
