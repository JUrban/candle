(* ========================================================================== *)
(* Analytic invariant for the exact packed object-state representation.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast checker keeps a center value and     *)
(* gradient, a whole-box value and gradient, and one packed whole-box         *)
(* Hessian.  This is intentionally not the older fixed-rounding Taylor-result *)
(* representation: it is the semantic shape of the exact object-q witness     *)
(* produced by the verified fixed-word refinement.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_complete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_invariant = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_complete_sound;;

let candle_q_packed_object_center_first_contains_def = new_definition
 `candle_q_packed_object_center_first_contains
      center_value center_gradient environment e <=>
    candle_q_interval_contains center_value
      (candle_analytic_value environment e) /\
    (!i. i < 6
         ==> candle_q_interval_contains
               (candle_q_interval_lookup i center_gradient)
               (candle_analytic_d i environment e))`;;

let candle_q_packed_object_center_jet_def = new_definition
 `candle_q_packed_object_center_jet
      center_value center_gradient packed_hessian =
    candle_q_dim_jet_make center_value center_gradient
      (candle_q_packed_hessian6_expand packed_hessian)`;;

let candle_q_packed_object_box_jet_def = new_definition
 `candle_q_packed_object_box_jet
      value_bound gradient_bounds packed_hessian =
    candle_q_dim_jet_make value_bound gradient_bounds
      (candle_q_packed_hessian6_expand packed_hessian)`;;

let candle_q_packed_object_item_analytic_invariant_def = new_definition
 `candle_q_packed_object_item_analytic_invariant
      center_boxes outer_boxes domain center_value center_gradient
      value_bound gradient_bounds packed_hessian center_e box_e <=>
    candle_analytic_valid_dim 6 box_e /\
    candle_analytic_erase_sqrt_certificates center_e =
      candle_analytic_erase_sqrt_certificates box_e /\
    (domain ==>
       LENGTH center_gradient = 6 /\
       candle_q_dim_jet_shape 6
         (candle_q_packed_object_box_jet
           value_bound gradient_bounds packed_hessian) /\
       (!environment.
          candle_q_stack_contains center_boxes environment
          ==> candle_analytic_regular_at environment center_e /\
              candle_q_packed_object_center_first_contains
                center_value center_gradient environment center_e) /\
       (!environment.
          candle_q_stack_contains outer_boxes environment
          ==> candle_analytic_regular_at environment box_e /\
              candle_q_dim_analytic_contains 6
                (candle_q_packed_object_box_jet
                  value_bound gradient_bounds packed_hessian)
                environment box_e))`;;

let candle_q_packed_object_center_jet_shape = prove
 (`!center_value center_gradient packed_hessian.
     LENGTH center_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_center_jet
         center_value center_gradient packed_hessian)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let matrix_shape =
    ISPEC
      `packed_hessian:
        (((num#num)#num)#((num#num)#num))list`
      candle_q_packed_hessian6_expand_shape in
  REWRITE_TAC[candle_q_packed_object_center_jet_def;
              candle_q_dim_jet_shape_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  ASM_REWRITE_TAC[] THEN
  ACCEPT_TAC matrix_shape);;

let candle_q_packed_object_center_complete_contains = prove
 (`!center_value center_gradient value_bound gradient_bounds packed_hessian
       environment center_e box_e.
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_packed_object_center_first_contains
       center_value center_gradient environment center_e /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian)
       environment box_e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_center_jet
         center_value center_gradient packed_hessian)
       environment center_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains 6
      (candle_q_packed_object_box_jet
        value_bound gradient_bounds packed_hessian)
      environment center_e`
  ASSUME_TAC THENL
   [MP_TAC
      (MATCH_MP
        (ISPECL
          [`6`;
           `candle_q_packed_object_box_jet
             value_bound gradient_bounds packed_hessian`;
           `environment:real list`;
           `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
          candle_q_dim_analytic_contains_certificate_transport)
        (ASSUME
          `candle_analytic_erase_sqrt_certificates center_e =
           candle_analytic_erase_sqrt_certificates box_e`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_center_first_contains_def;
       candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_center_jet_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_hessian_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_hessian_def;
       candle_q_dim_jet_make_def; FST; SND]) THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_center_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_object_source_center_in_interval = prove
 (`!source_boxes.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_box_valid_list source_boxes
     ==>
     (candle_q_box_center_vector source_boxes : real^N) IN
       interval
         [candle_q_box_lower_vector source_boxes,
          candle_q_box_upper_vector source_boxes]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i IN 1..dimindex (:N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 < LENGTH
      (source_boxes:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_box_lower_vector_component;
               candle_q_box_upper_vector_component;
               candle_q_box_center_vector_component] THEN
  MP_TAC
    (SPEC
      `EL (i - 1)
        (source_boxes:(((num#num)#num)#((num#num)#num))list)`
      candle_q_box_midpoint_radius) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC candle_q_box_valid_list_el THEN
    ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

let candle_q_packed_object_outer_vector_invariant = prove
 (`!outer_boxes box_jet box_e.
     LENGTH outer_boxes = 6 /\
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment box_e /\
            candle_q_dim_analytic_contains 6 box_jet environment box_e)
     ==>
     (!(z:real^6). z IN interval
          [candle_q_box_lower_vector outer_boxes,
           candle_q_box_upper_vector outer_boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. z$(k + 1)) 6) box_e) /\
     (!(z:real^6). z IN interval
          [candle_q_box_lower_vector outer_boxes,
           candle_q_box_upper_vector outer_boxes]
        ==> candle_q_dim_analytic_contains 6 box_jet
              (list_of_seq (\k. z$(k + 1)) 6) box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `z:real^6` THEN DISCH_TAC THEN
  let outer_stack =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (ISPECL
          [`outer_boxes:
             (((num#num)#num)#((num#num)#num))list`;
           `z:real^6`]
          candle_q_box_stack_contains_vector))
      (CONJ
        (ASSUME
          `LENGTH
            (outer_boxes:
              (((num#num)#num)#((num#num)#num))list) = 6`)
        (ASSUME
          `(z:real^6) IN interval
            [candle_q_box_lower_vector outer_boxes,
             candle_q_box_upper_vector outer_boxes]`)) in
  let outer_at_z =
    MATCH_MP
      (SPEC
        `list_of_seq (\k. (z:real^6)$(k + 1)) 6`
        (ASSUME
          `!environment.
             candle_q_stack_contains outer_boxes environment
             ==> candle_analytic_regular_at environment box_e /\
                 candle_q_dim_analytic_contains 6 box_jet
                   environment box_e`))
      outer_stack in
  MP_TAC outer_at_z THEN MESON_TAC[]);;

let candle_q_packed_object_item_complete_analytic_invariant = prove
 (`!source_boxes center_boxes outer_boxes radii domain
       center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     LENGTH source_boxes = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant (ARB:real^6)
       source_boxes
       (candle_q_dim_taylor_model_result_complete radii domain
         (candle_q_packed_object_center_jet
           center_value center_gradient packed_hessian)
         (candle_q_packed_hessian6_expand packed_hessian))
       center_e box_e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
        (LABEL_TAC "object_invariant"))) THEN
  USE_THEN "object_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "domain_invariant"))) THEN
    let geometry =
    MATCH_MP
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (SPECL
            [`source_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `center_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `outer_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `radii:((num#num)#num)list`]
            (INST_TYPE [`:6`,`:N`]
              candle_q_packed_source_correspondence_handoff)))
      (CONJ
        (ASSUME
          `LENGTH
            (source_boxes:
              (((num#num)#num)#((num#num)#num))list) = 6`)
        (ASSUME
          `candle_q_packed_source_correspondence
            source_boxes center_boxes outer_boxes radii`)) in
  let center_stack,geometry_rest = CONJ_PAIR geometry in
  let _,source_subset_outer = CONJ_PAIR geometry_rest in
  ASSUME_TAC center_stack THEN ASSUME_TAC source_subset_outer THEN
  MP_TAC
    (ASSUME
      `candle_q_packed_source_correspondence
        source_boxes center_boxes outer_boxes radii`) THEN
  REWRITE_TAC[candle_q_packed_source_correspondence_def;
              candle_q_packed_center_contains_source_midpoint_def;
              candle_q_packed_outer_covers_source_def] THEN
  STRIP_TAC THEN
    MATCH_MP_TAC
      (REWRITE_RULE
        [candle_q_packed_object_box_jet_def;
         candle_q_dim_jet_hessian_def; candle_q_dim_jet_make_def; FST; SND]
        (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
          (ISPECL
            [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
             `source_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `center_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `outer_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `radii:((num#num)#num)list`; `domain:bool`;
             `candle_q_packed_object_center_jet
               center_value center_gradient packed_hessian`;
             `candle_q_packed_object_box_jet
               value_bound gradient_bounds packed_hessian`;
             `ARB:real^6`]
            candle_q_dim_taylor_model_packed_complete_analytic_invariant))) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "valid" ACCEPT_TAC;
    USE_THEN "erasure" ACCEPT_TAC;
    USE_THEN "source_length" ACCEPT_TAC;
    USE_THEN "correspondence" ACCEPT_TAC;
    DISCH_TAC THEN
      USE_THEN "domain_invariant"
      (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_gradient_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "box_shape")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_all")
            (LABEL_TAC "outer_all")))) THEN
    let midpoint_environment =
      `list_of_seq
        (\k. (candle_q_box_center_vector source_boxes : real^6)$(k + 1))
        6` in
      let center_at_midpoint =
      MATCH_MP
        (SPEC midpoint_environment
          (ASSUME
            `!environment.
               candle_q_stack_contains center_boxes environment
               ==> candle_analytic_regular_at environment center_e /\
                   candle_q_packed_object_center_first_contains
                     center_value center_gradient environment center_e`))
        (ASSUME
          `candle_q_stack_contains center_boxes
            (list_of_seq
              (\k.
                (candle_q_box_center_vector source_boxes : real^6)$(k + 1))
              6)`) in
    let source_valid =
      ASSUME `candle_q_box_valid_list source_boxes` in
      let midpoint_in_source =
      MATCH_MP
        (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
          (SPEC
            `source_boxes:
              (((num#num)#num)#((num#num)#num))list`
            (INST_TYPE [`:6`,`:N`]
              candle_q_packed_object_source_center_in_interval)))
        (CONJ
          (ASSUME
            `LENGTH
              (source_boxes:
                (((num#num)#num)#((num#num)#num))list) = 6`)
          source_valid) in
    let midpoint_in_outer =
      MATCH_MP
        (REWRITE_RULE[SUBSET]
          (ASSUME
            `interval
              [candle_q_box_lower_vector source_boxes,
               candle_q_box_upper_vector source_boxes : real^6]
             SUBSET
             interval
              [candle_q_box_lower_vector outer_boxes,
               candle_q_box_upper_vector outer_boxes]`))
        midpoint_in_source in
      let outer_stack_midpoint_rule =
      CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (ISPECL
          [`outer_boxes:
             (((num#num)#num)#((num#num)#num))list`;
           `candle_q_box_center_vector source_boxes:real^6`]
          candle_q_box_stack_contains_vector) in
    let outer_stack_midpoint_premise =
      CONJ
        (REWRITE_RULE
          [ASSUME
            `LENGTH
              (source_boxes:
                (((num#num)#num)#((num#num)#num))list) = 6`]
          (ASSUME
            `LENGTH
              (outer_boxes:
                (((num#num)#num)#((num#num)#num))list) =
             LENGTH
               (source_boxes:
                 (((num#num)#num)#((num#num)#num))list)`))
        midpoint_in_outer in
      let outer_stack_at_midpoint =
      MATCH_MP
        outer_stack_midpoint_rule outer_stack_midpoint_premise in
    let outer_at_midpoint =
      MATCH_MP
        (SPEC midpoint_environment
          (ASSUME
            `!environment.
               candle_q_stack_contains outer_boxes environment
               ==> candle_analytic_regular_at environment box_e /\
                   candle_q_dim_analytic_contains 6
                     (candle_q_packed_object_box_jet
                       value_bound gradient_bounds packed_hessian)
                     environment box_e`))
        outer_stack_at_midpoint in
      let center_regular,center_first = CONJ_PAIR center_at_midpoint in
      let _,outer_contains_midpoint = CONJ_PAIR outer_at_midpoint in
      let center_shape =
        MATCH_MP
          (SPECL
            [`center_value:((num#num)#num)#((num#num)#num)`;
             `center_gradient:
               (((num#num)#num)#((num#num)#num))list`;
             `packed_hessian:
               (((num#num)#num)#((num#num)#num))list`]
            candle_q_packed_object_center_jet_shape)
          (ASSUME
            `LENGTH
              (center_gradient:
                (((num#num)#num)#((num#num)#num))list) = 6`) in
      let center_complete =
        MATCH_MP
          (SPECL
            [`center_value:((num#num)#num)#((num#num)#num)`;
             `center_gradient:
               (((num#num)#num)#((num#num)#num))list`;
             `value_bound:((num#num)#num)#((num#num)#num)`;
             `gradient_bounds:
               (((num#num)#num)#((num#num)#num))list`;
             `packed_hessian:
               (((num#num)#num)#((num#num)#num))list`;
             midpoint_environment;
             `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
            candle_q_packed_object_center_complete_contains)
          (CONJ
            (ASSUME
              `candle_analytic_erase_sqrt_certificates center_e =
               candle_analytic_erase_sqrt_certificates box_e`)
            (CONJ center_first outer_contains_midpoint)) in
      let outer_length =
        REWRITE_RULE
          [ASSUME
            `LENGTH
              (source_boxes:
                (((num#num)#num)#((num#num)#num))list) = 6`]
          (ASSUME
            `LENGTH
              (outer_boxes:
                (((num#num)#num)#((num#num)#num))list) =
             LENGTH
               (source_boxes:
                 (((num#num)#num)#((num#num)#num))list)`) in
      let outer_vector_invariant =
        MATCH_MP
          (ISPECL
            [`outer_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `candle_q_packed_object_box_jet
               value_bound gradient_bounds packed_hessian`;
             `box_e:candle_analytic_expr`]
            candle_q_packed_object_outer_vector_invariant)
          (CONJ outer_length
            (ASSUME
              `!environment.
                 candle_q_stack_contains outer_boxes environment
                 ==> candle_analytic_regular_at environment box_e /\
                     candle_q_dim_analytic_contains 6
                       (candle_q_packed_object_box_jet
                         value_bound gradient_bounds packed_hessian)
                       environment box_e`)) in
      let outer_regular,outer_contains = CONJ_PAIR outer_vector_invariant in
      let final_invariant =
        end_itlist CONJ
          [center_regular; outer_regular; center_shape; center_complete;
           ASSUME
             `candle_q_dim_jet_shape 6
               (candle_q_packed_object_box_jet
                 value_bound gradient_bounds packed_hessian)`;
             outer_contains] in
      ACCEPT_TAC
        (REWRITE_RULE
          [candle_q_packed_object_box_jet_def;
           candle_q_dim_jet_make_def]
          final_invariant)]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_center_jet_shape;
     candle_q_packed_object_center_complete_contains;
     candle_q_packed_object_source_center_in_interval;
     candle_q_packed_object_outer_vector_invariant;
     candle_q_packed_object_item_complete_analytic_invariant] then
  failwith "packed object invariant: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_INVARIANT_OK DEVELOPMENT_NON_RELEASE";;

end;;
