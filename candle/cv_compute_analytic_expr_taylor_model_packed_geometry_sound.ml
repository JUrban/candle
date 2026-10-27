(* ========================================================================== *)
(* Scale-independent geometry for externally packed Taylor cells.            *)
(*                                                                            *)
(* The fast packed checker uses scale 2^40, while the earlier fixed-scale     *)
(* implementation used 10^12.  The analytic handoff therefore meets at the   *)
(* exact rational [candle_q] representation, not at either fixed encoding.    *)
(* This file records two reusable parts of that handoff.  First, any exact    *)
(* rational radii which dominate the canonical source-box radii establish     *)
(* the same [m_cell_domain] contract, independently of their source scale.    *)
(* This is the stronger, common-center route; it is not inferred merely from  *)
(* the packed checker's interval-center geometry.  Second, independently, an  *)
(* authenticated outer-box correspondence transports source-box membership.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_semantics.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_geometry_sound = struct

open Multivariate_taylor;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_taylor_model_semantics;;

let candle_q_packed_radii_cover_source_def = new_definition
 `candle_q_packed_radii_cover_source source_boxes radii <=>
    LENGTH radii = LENGTH source_boxes /\
    (!k. k < LENGTH source_boxes
         ==> candle_q_real (EL k (candle_q_radius_list source_boxes)) <=
             candle_q_real (EL k radii))`;;

let candle_q_packed_outer_covers_source_def = new_definition
 `candle_q_packed_outer_covers_source source_boxes outer_boxes <=>
    LENGTH outer_boxes = LENGTH source_boxes /\
    (!k. k < LENGTH source_boxes
         ==> candle_q_real (FST (EL k outer_boxes)) <=
             candle_q_real (FST (EL k source_boxes)) /\
             candle_q_real (SND (EL k source_boxes)) <=
             candle_q_real (SND (EL k outer_boxes)))`;;

let candle_q_packed_center_contains_source_midpoint_def = new_definition
 `candle_q_packed_center_contains_source_midpoint
      source_boxes center_boxes <=>
    LENGTH center_boxes = LENGTH source_boxes /\
    (!k. k < LENGTH source_boxes
         ==> candle_q_interval_contains (EL k center_boxes)
               (candle_q_real
                 (candle_q_midpoint (EL k source_boxes))))`;;

let candle_q_packed_source_correspondence_def = new_definition
 `candle_q_packed_source_correspondence
      source_boxes center_boxes outer_boxes radii <=>
    candle_q_box_valid_list source_boxes /\
    candle_q_packed_center_contains_source_midpoint
      source_boxes center_boxes /\
    candle_q_packed_radii_cover_source source_boxes radii /\
    candle_q_packed_outer_covers_source source_boxes outer_boxes`;;

let candle_q_packed_radii_m_cell_domain = prove
 (`!source_boxes radii.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_box_valid_list source_boxes /\
     candle_q_packed_radii_cover_source source_boxes radii
     ==>
     m_cell_domain
       (candle_q_box_lower_vector source_boxes,
        candle_q_box_upper_vector source_boxes : real^N)
       (candle_q_box_center_vector source_boxes)
       (candle_q_list_real_vector radii)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_radii_cover_source_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "source_valid")
        (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
          (LABEL_TAC "radius_cover")))) THEN
  USE_THEN "source_length"
    (fun source_length ->
      USE_THEN "source_valid"
        (fun source_valid ->
          MP_TAC
            (MATCH_MP
              (ISPEC
                `source_boxes:(((num#num)#num)#((num#num)#num))list`
                candle_q_box_m_cell_domain)
              (CONJ source_length source_valid)))) THEN
  REWRITE_TAC[m_cell_domain] THEN
  DISCH_THEN (LABEL_TAC "source_domain") THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "source_domain"
    (fun source_domain ->
      MP_TAC
        (MATCH_MP (SPEC `i:num` source_domain)
          (ASSUME `i IN 1..dimindex (:N)`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_lower_center")
      (CONJUNCTS_THEN2 (LABEL_TAC "source_center_upper")
        (LABEL_TAC "source_radius"))) THEN
  CONJ_TAC THENL
   [USE_THEN "source_lower_center" ACCEPT_TAC;
    CONJ_TAC THENL
     [USE_THEN "source_center_upper" ACCEPT_TAC;
      ALL_TAC]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(candle_q_box_radius_vector source_boxes : real^N)$i` THEN
  CONJ_TAC THENL
   [USE_THEN "source_radius" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `i - 1 <
      LENGTH
        (source_boxes:(((num#num)#num)#((num#num)#num))list)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real
      (EL (i - 1) (candle_q_radius_list source_boxes)) =
    (candle_q_box_radius_vector source_boxes : real^N)$i`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [MATCH_MP_TAC candle_q_radius_list_vector_component THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(candle_q_list_real_vector radii : real^N)$i =
    candle_q_real (EL (i - 1) radii)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_list_real_vector_component THEN
    UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  USE_THEN "radius_cover"
    (fun radius_cover ->
      MATCH_ACCEPT_TAC
        (MATCH_MP (SPEC `i - 1` radius_cover)
          (ASSUME
            `i - 1 <
             LENGTH
               (source_boxes:
                 (((num#num)#num)#((num#num)#num))list)`))));;

let candle_q_packed_radii_m_cell_domain_same_scale = prove
 (`!source_boxes radii.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_box_valid_list source_boxes /\
     LENGTH radii = LENGTH source_boxes /\
     (!k. k < LENGTH source_boxes
          ==> candle_q_real (EL k (candle_q_radius_list source_boxes)) <=
              candle_q_real (EL k radii))
     ==>
     m_cell_domain
       (candle_q_box_lower_vector source_boxes,
        candle_q_box_upper_vector source_boxes : real^N)
       (candle_q_box_center_vector source_boxes)
       (candle_q_list_real_vector radii)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_radii_m_cell_domain THEN
  ASM_REWRITE_TAC[candle_q_packed_radii_cover_source_def]);;

let candle_q_packed_outer_interval_subset = prove
 (`!source_boxes outer_boxes.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_packed_outer_covers_source source_boxes outer_boxes
     ==>
     interval
       [candle_q_box_lower_vector source_boxes,
        candle_q_box_upper_vector source_boxes : real^N]
     SUBSET
     interval
       [candle_q_box_lower_vector outer_boxes,
        candle_q_box_upper_vector outer_boxes]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_outer_covers_source_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
        (LABEL_TAC "outer_cover"))) THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
  X_GEN_TAC `p:real^N` THEN DISCH_THEN (LABEL_TAC "p_in_source") THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "p_in_source"
    (fun p_in_source ->
      MP_TAC
        (MATCH_MP (SPEC `i:num` p_in_source)
          (ASSUME `1 <= i /\ i <= dimindex (:N)`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_lower_p")
      (LABEL_TAC "p_source_upper")) THEN
  SUBGOAL_THEN `i IN 1..dimindex (:N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `i - 1 <
      LENGTH
        (source_boxes:(((num#num)#num)#((num#num)#num))list)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= i /\ i <= dimindex (:N)` THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "outer_cover"
    (fun outer_cover ->
      MP_TAC
        (MATCH_MP (SPEC `i - 1` outer_cover)
          (ASSUME
            `i - 1 <
             LENGTH
               (source_boxes:
                 (((num#num)#num)#((num#num)#num))list)`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "outer_lower_source")
      (LABEL_TAC "source_upper_outer")) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `(candle_q_box_lower_vector source_boxes : real^N)$i` THEN
    ASM_SIMP_TAC[candle_q_box_lower_vector_component];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `(candle_q_box_upper_vector source_boxes : real^N)$i` THEN
    ASM_SIMP_TAC[candle_q_box_upper_vector_component]]);;

let candle_q_packed_center_contains_source_midpoint_stack = prove
 (`!source_boxes center_boxes.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_packed_center_contains_source_midpoint
       source_boxes center_boxes
     ==>
     candle_q_stack_contains center_boxes
       (list_of_seq
         (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_center_contains_source_midpoint_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_q_box_stack_contains_vector THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTERVAL] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `i - 1 <
       LENGTH
         (source_boxes:(((num#num)#num)#((num#num)#num))list)`
     ASSUME_TAC THENL
     [UNDISCH_TAC `1 <= i /\ i <= dimindex (:N)` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `i - 1`) THEN
    ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN
    ASM_SIMP_TAC[candle_q_box_lower_vector_component;
                 candle_q_box_upper_vector_component;
                 candle_q_box_center_vector_component; IN_NUMSEG]]);;

let candle_q_packed_source_correspondence_handoff = prove
 (`!source_boxes center_boxes outer_boxes radii.
     LENGTH source_boxes = dimindex (:N) /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii
     ==>
     candle_q_stack_contains center_boxes
       (list_of_seq
         (\k. (candle_q_box_center_vector source_boxes : real^N)$(k + 1))
         (dimindex (:N))) /\
     m_cell_domain
       (candle_q_box_lower_vector source_boxes,
        candle_q_box_upper_vector source_boxes : real^N)
       (candle_q_box_center_vector source_boxes)
       (candle_q_list_real_vector radii) /\
     interval
       [candle_q_box_lower_vector source_boxes,
        candle_q_box_upper_vector source_boxes : real^N]
     SUBSET
     interval
       [candle_q_box_lower_vector outer_boxes,
        candle_q_box_upper_vector outer_boxes]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_correspondence_def;
              candle_q_packed_center_contains_source_midpoint_def] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_packed_center_contains_source_midpoint_stack THEN
    ASM_REWRITE_TAC[candle_q_packed_center_contains_source_midpoint_def];
    MATCH_MP_TAC candle_q_packed_radii_m_cell_domain THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_outer_interval_subset THEN
    ASM_REWRITE_TAC[]]);;

print_endline
  "CANDLE_CV_PACKED_GEOMETRY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
