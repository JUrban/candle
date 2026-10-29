(* ========================================================================== *)
(* Faithful completed-object handoff for the exact packed source checker.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source replay authenticates the center   *)
(* value and gradient together with a packed whole-box Hessian.  The final   *)
(* fast object checker completes its value and gradient directly from those  *)
(* fields.  These theorems prove that the faithful completed fields satisfy  *)
(* the ordinary analytic-result invariant on the authenticated source cell.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_value_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_gradient_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_complete_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_object_complete_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_flyspeck_bridge;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_value_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;

let candle_q_packed_object_complete6_box_jet_shape = prove
 (`!radii center_value center_gradient packed_hessian.
     LENGTH center_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_dim_jet_make
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed_hessian)
         (candle_q_packed_object_gradient_complete6
           radii center_gradient packed_hessian)
         (candle_q_packed_hessian6_expand packed_hessian))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    ASM_REWRITE_TAC[];
    MP_TAC
      (ISPEC
        `packed_hessian:
          (((num#num)#num)#((num#num)#num))list`
        candle_q_packed_hessian6_expand_shape) THEN
    MESON_TAC[]]);;

let candle_q_packed_object_complete6_pointwise_analytic_contains = prove
 (`!e (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed_hessian (p:real^6).
     candle_analytic_valid_dim 6 e /\
     candle_analytic_regular_at
       (list_of_seq (\k. p$(k + 1)) 6) e /\
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) (candle_analytic_denote_dim e) /\
     candle_q_interval_contains center_value
       (candle_analytic_denote_dim e y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains
             (candle_q_packed_hessian6_expand packed_hessian)
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1)
                   (candle_analytic_denote_dim e) z) 6) 6)) /\
     p IN interval [lower,upper]
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_dim_jet_make
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed_hessian)
         (candle_q_packed_object_gradient_complete6
           radii center_gradient packed_hessian)
         (candle_q_packed_hessian6_expand packed_hessian))
       (list_of_seq (\k. p$(k + 1)) 6) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let completed_jet =
    `candle_q_dim_jet_make
      (candle_q_packed_object_value_bound6
        radii center_value center_gradient packed_hessian)
      (candle_q_packed_object_gradient_complete6
        radii center_gradient packed_hessian)
      (candle_q_packed_hessian6_expand packed_hessian)` in
  let completed_shape =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_complete6_box_jet_shape)
      (ASSUME
        `LENGTH
          (center_gradient:
            (((num#num)#num)#((num#num)#num))list) = 6`) in
  let value_contains =
    MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim e:real^6->real`;
         `lower:real^6`; `upper:real^6`; `y:real^6`;
         `radii:((num#num)#num)list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `p:real^6`]
        candle_q_packed_object_value_bound6_flyspeck_contains)
      (end_itlist CONJ
        [ASSUME `LENGTH (radii:((num#num)#num)list) = 6`;
         ASSUME `ALL (\r. &0 <= candle_q_real r) radii`;
         ASSUME
           `m_cell_domain ((lower:real^6),upper) y
             (candle_q_list_real_vector radii)`;
         ASSUME
           `diff2_domain ((lower:real^6),upper)
             (candle_analytic_denote_dim e)`;
         ASSUME
           `candle_q_interval_contains center_value
             (candle_analytic_denote_dim e (y:real^6))`;
         ASSUME
           `candle_q_stack_contains center_gradient
             (list_of_seq
               (\di. partial (di + 1) (candle_analytic_denote_dim e)
                 (y:real^6)) 6)`;
         ASSUME
           `!(z:real^6). z IN interval [lower,upper]
             ==> ALL2 candle_q_stack_contains
                   (candle_q_packed_hessian6_expand packed_hessian)
                   (list_of_seq
                     (\di. list_of_seq
                       (\dj. partial2 (dj + 1) (di + 1)
                         (candle_analytic_denote_dim e) z) 6) 6)`;
         ASSUME `(p:real^6) IN interval [lower,upper]`]) in
  let gradient_contains =
    MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim e:real^6->real`;
         `lower:real^6`; `upper:real^6`; `y:real^6`;
         `radii:((num#num)#num)list`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `p:real^6`]
        candle_q_packed_object_gradient_complete6_sound)
      (end_itlist CONJ
        [ASSUME `LENGTH (radii:((num#num)#num)list) = 6`;
         ASSUME
           `LENGTH
             (center_gradient:
               (((num#num)#num)#((num#num)#num))list) = 6`;
         ASSUME `ALL (\r. &0 <= candle_q_real r) radii`;
         ASSUME
           `m_cell_domain ((lower:real^6),upper) y
             (candle_q_list_real_vector radii)`;
         ASSUME
           `diff2_domain ((lower:real^6),upper)
             (candle_analytic_denote_dim e)`;
         ASSUME
           `candle_q_stack_contains center_gradient
             (list_of_seq
               (\di. partial (di + 1) (candle_analytic_denote_dim e)
                 (y:real^6)) 6)`;
         ASSUME
           `!(z:real^6). z IN interval [lower,upper]
             ==> ALL2 candle_q_stack_contains
                   (candle_q_packed_hessian6_expand packed_hessian)
                   (list_of_seq
                     (\di. list_of_seq
                       (\dj. partial2 (dj + 1) (di + 1)
                         (candle_analytic_denote_dim e) z) 6) 6)`;
         ASSUME `(p:real^6) IN interval [lower,upper]`]) in
  let hessian_contains =
    MATCH_MP
      (SPEC `p:real^6`
        (ASSUME
          `!(z:real^6). z IN interval [lower,upper]
            ==> ALL2 candle_q_stack_contains
                  (candle_q_packed_hessian6_expand packed_hessian)
                  (list_of_seq
                    (\di. list_of_seq
                      (\dj. partial2 (dj + 1) (di + 1)
                        (candle_analytic_denote_dim e) z) 6) 6)`))
      (ASSUME `(p:real^6) IN interval [lower,upper]`) in
  let components =
    MATCH_MP
      (REWRITE_RULE
        [candle_q_dim_jet_f_def; candle_q_dim_jet_gradient_def;
         candle_q_dim_jet_hessian_def; candle_q_dim_jet_make_def; FST; SND]
        (BETA_RULE
          (ISPECL
            [`6`; completed_jet;
             `candle_analytic_denote_dim e (p:real^6)`;
             `(\di. partial (di + 1) (candle_analytic_denote_dim e)
                (p:real^6)):num->real`;
             `(\di dj. partial2 (dj + 1) (di + 1)
                (candle_analytic_denote_dim e) (p:real^6)):num->num->real`]
            candle_q_dim_jet_contains_components_of_stacks)))
      (BETA_RULE
        (end_itlist CONJ
          [REWRITE_RULE [candle_q_dim_jet_make_def] completed_shape;
           REWRITE_RULE
             [candle_q_dim_jet_f_def; candle_q_dim_jet_make_def; FST; SND]
             value_contains;
           REWRITE_RULE
             [candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND]
             gradient_contains;
           REWRITE_RULE
             [candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]
             hessian_contains])) in
  MATCH_MP_TAC
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE [`:6`,`:N`]
        candle_q_dim_flyspeck_components_analytic_contains)) THEN
  ASM_REWRITE_TAC[candle_q_dim_jet_make_def] THEN
  MATCH_ACCEPT_TAC components);;

let candle_q_packed_object_complete6_source_analytic_invariant = prove
 (`!source_boxes radii domain center_value center_gradient packed_hessian
       center_e box_e.
     candle_analytic_valid_dim 6 box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH source_boxes = 6 /\
     candle_q_box_valid_list source_boxes /\
     candle_q_packed_radii_cover_source source_boxes radii /\
     (domain ==>
       candle_analytic_regular_at
         (list_of_seq
           (\k. (candle_q_box_center_vector source_boxes:real^6)$
             (k + 1)) 6) center_e /\
       candle_q_dim_jet_shape 6
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed_hessian)) /\
       candle_q_dim_analytic_contains 6
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed_hessian))
         (list_of_seq
           (\k. (candle_q_box_center_vector source_boxes:real^6)$
             (k + 1)) 6) center_e /\
       (!(z:real^6). z IN interval
          [candle_q_box_lower_vector source_boxes,
           candle_q_box_upper_vector source_boxes]
         ==> candle_analytic_regular_at
               (list_of_seq (\k. z$(k + 1)) 6) box_e) /\
       (!(z:real^6). z IN interval
          [candle_q_box_lower_vector source_boxes,
           candle_q_box_upper_vector source_boxes]
         ==> ALL2 candle_q_stack_contains
               (candle_q_packed_hessian6_expand packed_hessian)
               (list_of_seq
                 (\di. list_of_seq
                   (\dj. partial2 (dj + 1) (di + 1)
                     (candle_analytic_denote_dim box_e) z) 6) 6)))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant (ARB:real^6)
       source_boxes
       (candle_q_dim_taylor_model_result_make domain
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed_hessian))
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed_hessian)
         (candle_q_packed_object_gradient_complete6
           radii center_gradient packed_hessian)
         (candle_q_packed_hessian6_expand packed_hessian))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
          (CONJUNCTS_THEN2 (LABEL_TAC "source_regular")
            (LABEL_TAC "hessian_contains"))))) THEN
  SUBGOAL_THEN
   `LENGTH
      (center_gradient:
        (((num#num)#num)#((num#num)#num))list) = 6`
   (LABEL_TAC "center_gradient_length") THENL
   [USE_THEN "center_shape" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_analytic_regular_at
      (list_of_seq
        (\k. (candle_q_box_center_vector source_boxes:real^6)$(k + 1)) 6)
      box_e`
   (LABEL_TAC "center_regular_box") THENL
   [MATCH_MP_TAC
      (fst
        (EQ_IMP_RULE
          (MATCH_MP
            (ISPECL
              [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
               `list_of_seq
                 (\k. (candle_q_box_center_vector source_boxes:real^6)$
                   (k + 1)) 6`]
              candle_analytic_regular_certificate_transport)
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains 6
      (candle_q_dim_jet_make center_value center_gradient
        (candle_q_packed_hessian6_expand packed_hessian))
      (list_of_seq
        (\k. (candle_q_box_center_vector source_boxes:real^6)$(k + 1)) 6)
      box_e`
   (LABEL_TAC "center_contains_box") THENL
   [MATCH_MP_TAC
      (fst
        (EQ_IMP_RULE
          (MATCH_MP
            (ISPECL
              [`6`;
               `candle_q_dim_jet_make center_value center_gradient
                 (candle_q_packed_hessian6_expand packed_hessian)`;
               `list_of_seq
                 (\k. (candle_q_box_center_vector source_boxes:real^6)$
                   (k + 1)) 6`;
               `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
              candle_q_dim_analytic_contains_certificate_transport)
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let center_value_contains =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          (ISPECL
            [`box_e:candle_analytic_expr`;
             `candle_q_dim_jet_make center_value center_gradient
               (candle_q_packed_hessian6_expand packed_hessian)`;
             `candle_q_box_center_vector source_boxes:real^6`]
            candle_q_dim_analytic_contains_denote_value)))
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_dim_jet_make center_value center_gradient
            (candle_q_packed_hessian6_expand packed_hessian))
          (list_of_seq
            (\k. (candle_q_box_center_vector source_boxes:real^6)$
              (k + 1)) 6) box_e`) in
  let center_gradient_contains =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          (ISPECL
            [`box_e:candle_analytic_expr`;
             `candle_q_dim_jet_make center_value center_gradient
               (candle_q_packed_hessian6_expand packed_hessian)`;
             `candle_q_box_center_vector source_boxes:real^6`]
            candle_q_dim_analytic_jet_gradient_flyspeck_contains)))
      (end_itlist CONJ
        [ASSUME `candle_analytic_valid_dim 6 box_e`;
         ASSUME
           `candle_analytic_regular_at
             (list_of_seq
               (\k. (candle_q_box_center_vector source_boxes:real^6)$
                 (k + 1)) 6) box_e`;
         ASSUME
           `candle_q_dim_jet_shape 6
             (candle_q_dim_jet_make center_value center_gradient
               (candle_q_packed_hessian6_expand packed_hessian))`;
         ASSUME
           `candle_q_dim_analytic_contains 6
             (candle_q_dim_jet_make center_value center_gradient
               (candle_q_packed_hessian6_expand packed_hessian))
             (list_of_seq
               (\k. (candle_q_box_center_vector source_boxes:real^6)$
                 (k + 1)) 6) box_e`]) in
  let center_value_contains =
    REWRITE_RULE
      [candle_q_dim_jet_f_def; candle_q_dim_jet_make_def; FST; SND]
      center_value_contains in
  let center_gradient_contains =
    REWRITE_RULE
      [candle_q_dim_jet_gradient_def; candle_q_dim_jet_make_def; FST; SND]
      center_gradient_contains in
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
  let cell_domain =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          (ISPECL
            [`source_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `radii:((num#num)#num)list`]
            candle_q_packed_radii_m_cell_domain)))
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (source_boxes:
               (((num#num)#num)#((num#num)#num))list) = 6`;
         ASSUME `candle_q_box_valid_list source_boxes`;
         ASSUME
           `candle_q_packed_radii_cover_source source_boxes radii`]) in
  let radii_length =
    let details =
      REWRITE_RULE[candle_q_packed_radii_cover_source_def]
        (ASSUME
          `candle_q_packed_radii_cover_source source_boxes radii`) in
    TRANS (CONJUNCT1 details)
      (ASSUME
        `LENGTH
          (source_boxes:
            (((num#num)#num)#((num#num)#num))list) = 6`) in
  let diff2 =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          (ISPECL
            [`box_e:candle_analytic_expr`;
             `candle_q_box_lower_vector source_boxes:real^6`;
             `candle_q_box_upper_vector source_boxes:real^6`]
            candle_q_dim_analytic_regular_diff2_domain_bounds)))
      (CONJ
        (ASSUME `candle_analytic_valid_dim 6 box_e`)
        (ASSUME
          `!(z:real^6). z IN interval
             [candle_q_box_lower_vector source_boxes,
              candle_q_box_upper_vector source_boxes]
            ==> candle_analytic_regular_at
                  (list_of_seq (\k. z$(k + 1)) 6) box_e`)) in
  let completed_shape =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_complete6_box_jet_shape)
      (ASSUME
        `LENGTH
          (center_gradient:
            (((num#num)#num)#((num#num)#num))list) = 6`) in
  let completed_contains =
    let p = `p:real^6` in
    let p_in =
      ASSUME
        `(p:real^6) IN interval
          [candle_q_box_lower_vector source_boxes,
           candle_q_box_upper_vector source_boxes]` in
    let regular_at_p =
      MATCH_MP
        (SPEC p
          (ASSUME
            `!(z:real^6). z IN interval
               [candle_q_box_lower_vector source_boxes,
                candle_q_box_upper_vector source_boxes]
              ==> candle_analytic_regular_at
                    (list_of_seq (\k. z$(k + 1)) 6) box_e`))
        p_in in
    let result =
      MATCH_MP
        (ISPECL
          [`box_e:candle_analytic_expr`;
           `candle_q_box_lower_vector source_boxes:real^6`;
           `candle_q_box_upper_vector source_boxes:real^6`;
           `candle_q_box_center_vector source_boxes:real^6`;
           `radii:((num#num)#num)list`;
           `center_value:((num#num)#num)#((num#num)#num)`;
           `center_gradient:
              (((num#num)#num)#((num#num)#num))list`;
           `packed_hessian:
              (((num#num)#num)#((num#num)#num))list`;
           p]
          candle_q_packed_object_complete6_pointwise_analytic_contains)
        (end_itlist CONJ
          [ASSUME `candle_analytic_valid_dim 6 box_e`;
           regular_at_p; radii_length;
           ASSUME
             `LENGTH
               (center_gradient:
                 (((num#num)#num)#((num#num)#num))list) = 6`;
           radii_nonnegative; cell_domain; diff2;
           center_value_contains; center_gradient_contains;
           ASSUME
             `!(z:real^6). z IN interval
                [candle_q_box_lower_vector source_boxes,
                 candle_q_box_upper_vector source_boxes]
               ==> ALL2 candle_q_stack_contains
                     (candle_q_packed_hessian6_expand packed_hessian)
                     (list_of_seq
                       (\di. list_of_seq
                         (\dj. partial2 (dj + 1) (di + 1)
                           (candle_analytic_denote_dim box_e) z) 6) 6)`;
           p_in]) in
    GEN p (DISCH (concl p_in) result) in
  ACCEPT_TAC
    (REWRITE_RULE
      [candle_q_dim_jet_make_def]
      (end_itlist CONJ
        [ASSUME
         `candle_analytic_regular_at
           (list_of_seq
             (\k. (candle_q_box_center_vector source_boxes:real^6)$
               (k + 1)) 6) center_e`;
       ASSUME
         `!(z:real^6). z IN interval
            [candle_q_box_lower_vector source_boxes,
             candle_q_box_upper_vector source_boxes]
           ==> candle_analytic_regular_at
                 (list_of_seq (\k. z$(k + 1)) 6) box_e`;
       ASSUME
         `candle_q_dim_jet_shape 6
           (candle_q_dim_jet_make center_value center_gradient
             (candle_q_packed_hessian6_expand packed_hessian))`;
       ASSUME
         `candle_q_dim_analytic_contains 6
           (candle_q_dim_jet_make center_value center_gradient
             (candle_q_packed_hessian6_expand packed_hessian))
           (list_of_seq
             (\k. (candle_q_box_center_vector source_boxes:real^6)$
               (k + 1)) 6) center_e`;
         completed_shape; completed_contains])));;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_complete6_box_jet_shape;
     candle_q_packed_object_complete6_pointwise_analytic_contains;
     candle_q_packed_object_complete6_source_analytic_invariant] then
  failwith "packed object faithful completion: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
