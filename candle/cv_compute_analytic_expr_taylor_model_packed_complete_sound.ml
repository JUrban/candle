(* ========================================================================== *)
(* Analytic completion for externally packed Taylor-cell geometry.          *)
(*                                                                            *)
(* The packed checker supplies center and outer jets, exact rational radii,  *)
(* and a source-box correspondence independently.  These theorems combine   *)
(* that evidence with the scale-independent Taylor completion theorem.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_exact_complete_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_geometry_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_complete_sound = struct

open Multivariate_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_taylor_model_exact_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;

let candle_q_packed_radii_cover_nonnegative = prove
 (`!source_boxes radii.
     candle_q_box_valid_list source_boxes /\
     candle_q_packed_radii_cover_source source_boxes radii
     ==>
     ALL (\r. &0 <= candle_q_real r) radii`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_radii_cover_source_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM ALL_EL] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `k < LENGTH
      (source_boxes:(((num#num)#num)#((num#num)#num))list)`
   ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `candle_q_real (EL k (candle_q_radius_list source_boxes))` THEN
  CONJ_TAC THENL
   [MP_TAC
      (REWRITE_RULE[GSYM ALL_EL]
        (MATCH_MP candle_q_radius_list_nonnegative
          (ASSUME `candle_q_box_valid_list source_boxes`))) THEN
    DISCH_THEN (MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[candle_q_radius_list_length];
    ASM_MESON_TAC[]]);;

let candle_q_dim_analytic_regular_diff2_domain_bounds = prove
 (`!e (lower:real^N) (upper:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     diff2_domain (lower,upper) (candle_analytic_denote_dim e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[diff2_domain] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC diff2c_imp_diff2 THEN
  MATCH_MP_TAC candle_analytic_denote_dim_diff2c THEN
  ASM_MESON_TAC[]);;

let candle_q_dim_analytic_contains_denote_value = prove
 (`!e jet (z:real^N).
     candle_q_dim_analytic_contains (dimindex (:N)) jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     candle_q_interval_contains (candle_q_dim_jet_f jet)
       (candle_analytic_denote_dim e z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_dim_analytic_contains_def;
     candle_q_dim_jet_contains_components_def;
     candle_analytic_denote_dim_def] THEN
  MESON_TAC[]);;

let candle_q_dim_analytic_jet_hessian_box_contains = prove
 (`!e jet (lower:real^N) (upper:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     candle_q_dim_jet_shape (dimindex (:N)) jet /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> candle_q_dim_analytic_contains (dimindex (:N)) jet
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e)
     ==>
     !(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains
             (candle_q_dim_jet_hessian jet)
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1)
                   (candle_analytic_denote_dim e) z)
                 (dimindex (:N)))
               (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`e:candle_analytic_expr`;
       `jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `z:real^N`]
      candle_q_dim_analytic_jet_hessian_flyspeck_contains) THEN
  ASM_MESON_TAC[]);;

let candle_q_dim_analytic_exact_taylor_proxy_contains = prove
 (`!e (lower:real^N) (upper:real^N) (y:real^N)
       radii (domain:bool) center_jet box_jet (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. y$(k + 1)) (dimindex (:N))) e /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) center_jet
       (list_of_seq (\k. y$(k + 1)) (dimindex (:N))) e /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e) /\
     p IN interval [lower,upper]
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_q_dim_taylor_model_result_complete
           radii domain center_jet (candle_q_dim_jet_hessian box_jet)))
       (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let diff2_rule =
    ISPECL
      [`e:candle_analytic_expr`; `lower:real^N`; `upper:real^N`]
      candle_q_dim_analytic_regular_diff2_domain_bounds in
  let diff2_premises =
    CONJ
      (ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`)
      (ASSUME
        `!(z:real^N). z IN interval [lower,upper]
          ==> candle_analytic_regular_at
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`) in
  LABEL_TAC "diff2" (MATCH_MP diff2_rule diff2_premises) THEN
  let center_value_rule =
    ISPECL
      [`e:candle_analytic_expr`;
       `center_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `y:real^N`]
      candle_q_dim_analytic_contains_denote_value in
  let center_value_th =
    MATCH_MP center_value_rule
      (ASSUME
        `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
          (list_of_seq (\k. (y:real^N)$(k + 1)) (dimindex (:N))) e`) in
  LABEL_TAC "center_value" center_value_th THEN
  let center_gradient_rule =
    ISPECL
      [`e:candle_analytic_expr`;
       `center_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `y:real^N`]
      candle_q_dim_analytic_jet_gradient_flyspeck_contains in
  let center_gradient_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME
         `candle_analytic_regular_at
           (list_of_seq (\k. (y:real^N)$(k + 1)) (dimindex (:N))) e`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
       ASSUME
         `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
           (list_of_seq (\k. (y:real^N)$(k + 1)) (dimindex (:N))) e`] in
  LABEL_TAC "center_gradient"
    (MATCH_MP center_gradient_rule center_gradient_premises) THEN
  let box_hessian_rule =
    ISPECL
      [`e:candle_analytic_expr`;
       `box_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `lower:real^N`; `upper:real^N`]
      candle_q_dim_analytic_jet_hessian_box_contains in
  let box_hessian_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       ASSUME
         `!(z:real^N). z IN interval [lower,upper]
           ==> candle_analytic_regular_at
                 (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
       ASSUME
         `!(z:real^N). z IN interval [lower,upper]
           ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                 (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`] in
  LABEL_TAC "box_hessian"
    (MATCH_MP box_hessian_rule box_hessian_premises) THEN
  let proxy_rule =
    ISPECL
      [`candle_analytic_denote_dim e:real^N->real`;
       `lower:real^N`; `upper:real^N`; `y:real^N`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `box_jet:
          (((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list)`;
       `p:real^N`]
      candle_q_exact_taylor_model_complete_proxy_contains in
  let proxy_premises =
    end_itlist CONJ
      [ASSUME
         `LENGTH (radii:((num#num)#num)list) = dimindex (:N)`;
       ASSUME
         `ALL (\r. &0 <= candle_q_real r)
            (radii:((num#num)#num)list)`;
       ASSUME
         `m_cell_domain ((lower:real^N),(upper:real^N)) (y:real^N)
            (candle_q_list_real_vector radii:real^N)`;
       ASSUME
         `diff2_domain ((lower:real^N),(upper:real^N))
            (candle_analytic_denote_dim e:real^N->real)`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
       ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
       ASSUME
         `candle_q_interval_contains (candle_q_dim_jet_f center_jet)
            ((candle_analytic_denote_dim e:real^N->real) (y:real^N))`;
       ASSUME
         `candle_q_stack_contains (candle_q_dim_jet_gradient center_jet)
            (list_of_seq
              (\di. partial (di + 1)
                (candle_analytic_denote_dim e:real^N->real) (y:real^N))
              (dimindex (:N)))`;
       ASSUME
         `!(z:real^N). z IN interval [lower,upper]
           ==> ALL2 candle_q_stack_contains
                 (candle_q_dim_jet_hessian box_jet)
                 (list_of_seq
                   (\di. list_of_seq
                     (\dj. partial2 (dj + 1) (di + 1)
                       (candle_analytic_denote_dim e) z)
                     (dimindex (:N)))
                   (dimindex (:N)))`;
       ASSUME
         `(p:real^N) IN interval [(lower:real^N),(upper:real^N)]`] in
  let proxy_components = MATCH_MP proxy_rule proxy_premises in
  let regular_at_p =
    MATCH_MP
      (SPEC `p:real^N`
        (ASSUME
          `!(z:real^N). z IN interval [lower,upper]
            ==> candle_analytic_regular_at
                  (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`))
      (ASSUME
        `(p:real^N) IN interval [(lower:real^N),(upper:real^N)]`) in
  let analytic_rule =
    ISPECL
      [`e:candle_analytic_expr`;
       `candle_q_dim_taylor_model_proxy
          (candle_q_dim_taylor_model_result_complete
            radii (domain:bool) center_jet
            (candle_q_dim_jet_hessian box_jet))`;
       `p:real^N`]
      candle_q_dim_flyspeck_components_analytic_contains in
  let analytic_premises =
    end_itlist CONJ
      [ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`;
       regular_at_p; proxy_components] in
  ACCEPT_TAC (MATCH_MP analytic_rule analytic_premises));;

let candle_subset_forall_imp_transport = prove
 (`!s t (P:A->bool).
     s SUBSET t /\ (!x. x IN t ==> P x)
     ==> !x. x IN s ==> P x`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let candle_q_dim_taylor_model_packed_complete_analytic_invariant = prove
 (`!center_e box_e source_boxes center_boxes outer_boxes radii
       (domain:bool) center_jet box_jet (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     (domain ==>
       candle_analytic_regular_at
         (list_of_seq
           (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       (!(z:real^N). z IN interval
            [candle_q_box_lower_vector outer_boxes,
             candle_q_box_upper_vector outer_boxes]
          ==> candle_analytic_regular_at
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e) /\
       candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
       candle_q_dim_analytic_contains (dimindex (:N)) center_jet
         (list_of_seq
           (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
       (!(z:real^N). z IN interval
            [candle_q_box_lower_vector outer_boxes,
             candle_q_box_upper_vector outer_boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness
       source_boxes
       (candle_q_dim_taylor_model_result_complete
         radii domain center_jet (candle_q_dim_jet_hessian box_jet))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let geometry_handoff =
    MATCH_MP
      (ISPECL
        [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_boxes:(((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`]
        candle_q_packed_source_correspondence_handoff)
      (CONJ
        (ASSUME
          `LENGTH
             (source_boxes:
               (((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`)
        (ASSUME
          `candle_q_packed_source_correspondence
            source_boxes center_boxes outer_boxes radii`)) in
  let _,geometry_rest = CONJ_PAIR geometry_handoff in
  let cell_domain,source_subset_outer = CONJ_PAIR geometry_rest in
  ASSUME_TAC cell_domain THEN ASSUME_TAC source_subset_outer THEN
  MP_TAC
    (ASSUME
      `candle_q_packed_source_correspondence
        source_boxes center_boxes outer_boxes radii`) THEN
  REWRITE_TAC[candle_q_packed_source_correspondence_def] THEN
  STRIP_TAC THEN
  let radii_nonnegative =
    MATCH_MP
      (ISPECL
        [`source_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`]
        candle_q_packed_radii_cover_nonnegative)
      (CONJ
        (ASSUME `candle_q_box_valid_list source_boxes`)
        (ASSUME
          `candle_q_packed_radii_cover_source source_boxes radii`)) in
  LABEL_TAC "radii_nonnegative" radii_nonnegative THEN
  let radii_cover_details =
    REWRITE_RULE[candle_q_packed_radii_cover_source_def]
      (ASSUME
        `candle_q_packed_radii_cover_source
          source_boxes (radii:((num#num)#num)list)`) in
  let radii_length_source,_ = CONJ_PAIR radii_cover_details in
  let radii_length =
    TRANS radii_length_source
      (ASSUME
        `LENGTH
           (source_boxes:
             (((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`) in
  LABEL_TAC "radii_length" radii_length THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_q_dim_taylor_model_result_complete_domain] THEN
  DISCH_TAC THEN
  let analytic_inputs =
    MATCH_MP
      (ASSUME
        `(domain:bool) ==>
          candle_analytic_regular_at
            (list_of_seq
              (\k.
                (candle_q_box_center_vector source_boxes : real^N)$
                  (k + 1))
              (dimindex (:N))) center_e /\
          (!(z:real^N). z IN interval
               [candle_q_box_lower_vector outer_boxes,
                candle_q_box_upper_vector outer_boxes]
             ==> candle_analytic_regular_at
                   (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e) /\
          candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
          candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k.
                (candle_q_box_center_vector source_boxes : real^N)$
                  (k + 1))
              (dimindex (:N))) center_e /\
          candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
          (!(z:real^N). z IN interval
               [candle_q_box_lower_vector outer_boxes,
                candle_q_box_upper_vector outer_boxes]
             ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                   (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e)`)
      (ASSUME `domain:bool`) in
  MP_TAC analytic_inputs THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_regular")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
            (CONJUNCTS_THEN2 (LABEL_TAC "box_shape")
              (LABEL_TAC "outer_contains")))))) THEN
  SUBGOAL_THEN
   `candle_analytic_regular_at
      (list_of_seq
        (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
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
                 (\k. (candle_q_box_center_vector source_boxes : real^N)$
                   (k + 1))
                 (dimindex (:N))`]
              candle_analytic_regular_certificate_transport)
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
      (list_of_seq
        (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
        (dimindex (:N))) box_e`
   (LABEL_TAC "center_contains_box") THENL
   [MATCH_MP_TAC
      (fst
        (EQ_IMP_RULE
          (MATCH_MP
            (ISPECL
              [`dimindex (:N)`;
               `center_jet:
                  (((num#num)#num)#((num#num)#num))#
                  ((((num#num)#num)#((num#num)#num))list#
                   ((((num#num)#num)#((num#num)#num))list)list)`;
               `list_of_seq
                 (\k. (candle_q_box_center_vector source_boxes : real^N)$
                   (k + 1))
                 (dimindex (:N))`;
               `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
              candle_q_dim_analytic_contains_certificate_transport)
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let source_regular =
    MATCH_MP
      (BETA_RULE
        (ISPECL
          [`interval
             [(candle_q_box_lower_vector source_boxes:real^N),
              (candle_q_box_upper_vector source_boxes:real^N)]`;
           `interval
             [(candle_q_box_lower_vector outer_boxes:real^N),
              (candle_q_box_upper_vector outer_boxes:real^N)]`;
           `(\z:real^N.
              candle_analytic_regular_at
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e)`]
          candle_subset_forall_imp_transport))
      (CONJ
        source_subset_outer
        (ASSUME
          `!(z:real^N). z IN interval
               [candle_q_box_lower_vector outer_boxes,
                candle_q_box_upper_vector outer_boxes]
             ==> candle_analytic_regular_at
                   (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e`)) in
  LABEL_TAC "source_regular" source_regular THEN
  let source_contains =
    MATCH_MP
      (BETA_RULE
        (ISPECL
          [`interval
             [(candle_q_box_lower_vector source_boxes:real^N),
              (candle_q_box_upper_vector source_boxes:real^N)]`;
           `interval
             [(candle_q_box_lower_vector outer_boxes:real^N),
              (candle_q_box_upper_vector outer_boxes:real^N)]`;
           `(\z:real^N.
              candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e)`]
          candle_subset_forall_imp_transport))
      (CONJ
        source_subset_outer
        (ASSUME
          `!(z:real^N). z IN interval
               [candle_q_box_lower_vector outer_boxes,
                candle_q_box_upper_vector outer_boxes]
             ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                   (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e`)) in
  LABEL_TAC "source_contains" source_contains THEN
  let center_regular_result =
    ASSUME
      `candle_analytic_regular_at
        (list_of_seq
          (\k.
            (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e` in
  let completed_center_shape =
    MATCH_MP
        (ISPECL
          [`dimindex (:N)`; `radii:((num#num)#num)list`; `domain:bool`;
           `center_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`;
           `box_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`]
          candle_q_dim_taylor_model_result_complete_center_shape)
        (ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`) in
  let center_components =
      REWRITE_RULE[candle_q_dim_analytic_contains_def]
        (ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k.
                (candle_q_box_center_vector source_boxes : real^N)$
                  (k + 1))
              (dimindex (:N))) center_e`) in
    let completed_center_components =
      MATCH_MP
        (ISPECL
          [`dimindex (:N)`; `radii:((num#num)#num)list`; `domain:bool`;
           `center_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`;
           `box_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`;
           `candle_analytic_value
              (list_of_seq
                (\k.
                  (candle_q_box_center_vector source_boxes : real^N)$
                    (k + 1))
                (dimindex (:N))) center_e`;
           `(\di. candle_analytic_d di
              (list_of_seq
                (\k.
                  (candle_q_box_center_vector source_boxes : real^N)$
                    (k + 1))
                (dimindex (:N))) center_e):num->real`;
           `(\di dj. candle_analytic_dd di dj
              (list_of_seq
                (\k.
                  (candle_q_box_center_vector source_boxes : real^N)$
                    (k + 1))
                (dimindex (:N))) center_e):num->num->real`]
          candle_q_dim_taylor_model_result_complete_center_contains)
        (CONJ
          (ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)
          center_components) in
  let completed_center_result =
    REWRITE_RULE[GSYM candle_q_dim_analytic_contains_def]
      completed_center_components in
  let completed_proxy_shape =
    MATCH_MP
        (ISPECL
          [`dimindex (:N)`; `radii:((num#num)#num)list`; `domain:bool`;
           `center_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`;
           `box_jet:
              (((num#num)#num)#((num#num)#num))#
              ((((num#num)#num)#((num#num)#num))list#
               ((((num#num)#num)#((num#num)#num))list)list)`]
          candle_q_dim_taylor_model_result_complete_proxy_shape)
        (CONJ
          (ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)
          (ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`)) in
    let p_term = `p:real^N` in
    let p_in_source =
      ASSUME
        `(p:real^N) IN interval
          [(candle_q_box_lower_vector source_boxes:real^N),
           (candle_q_box_upper_vector source_boxes:real^N)]` in
    let pointwise_rule =
      ISPECL
        [`box_e:candle_analytic_expr`;
         `candle_q_box_lower_vector source_boxes:real^N`;
         `candle_q_box_upper_vector source_boxes:real^N`;
         `candle_q_box_center_vector source_boxes:real^N`;
         `radii:((num#num)#num)list`; `domain:bool`;
         `center_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `box_jet:
            (((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))list#
             ((((num#num)#num)#((num#num)#num))list)list)`;
         `p:real^N`]
        candle_q_dim_analytic_exact_taylor_proxy_contains in
    let pointwise_premises =
      end_itlist CONJ
        [ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_e`;
         ASSUME
           `candle_analytic_regular_at
             (list_of_seq
               (\k.
                 (candle_q_box_center_vector source_boxes : real^N)$
                   (k + 1))
               (dimindex (:N))) box_e`;
         ASSUME
           `!(z:real^N). z IN interval
                [candle_q_box_lower_vector source_boxes,
                 candle_q_box_upper_vector source_boxes]
              ==> candle_analytic_regular_at
                    (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e`;
         ASSUME
           `LENGTH (radii:((num#num)#num)list) = dimindex (:N)`;
         ASSUME
           `ALL (\r. &0 <= candle_q_real r)
              (radii:((num#num)#num)list)`;
         ASSUME
           `m_cell_domain
              ((candle_q_box_lower_vector source_boxes:real^N),
               (candle_q_box_upper_vector source_boxes:real^N))
              (candle_q_box_center_vector source_boxes:real^N)
              (candle_q_list_real_vector radii:real^N)`;
         ASSUME `candle_q_dim_jet_shape (dimindex (:N)) center_jet`;
         ASSUME
           `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
             (list_of_seq
               (\k.
                 (candle_q_box_center_vector source_boxes : real^N)$
                   (k + 1))
               (dimindex (:N))) box_e`;
         ASSUME `candle_q_dim_jet_shape (dimindex (:N)) box_jet`;
         ASSUME
           `!(z:real^N). z IN interval
                [candle_q_box_lower_vector source_boxes,
                 candle_q_box_upper_vector source_boxes]
              ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                    (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) box_e`;
         p_in_source] in
    let pointwise = MATCH_MP pointwise_rule pointwise_premises in
    let all_pointwise =
      GEN p_term (DISCH (concl p_in_source) pointwise) in
    ACCEPT_TAC
      (end_itlist CONJ
        [center_regular_result; source_regular; completed_center_shape;
         completed_center_result; completed_proxy_shape; all_pointwise]));;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_radii_cover_nonnegative;
     candle_q_dim_analytic_regular_diff2_domain_bounds;
     candle_q_dim_analytic_exact_taylor_proxy_contains;
     candle_subset_forall_imp_transport;
     candle_q_dim_taylor_model_packed_complete_analytic_invariant] then
  failwith "packed Taylor completion soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_TAYLOR_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
