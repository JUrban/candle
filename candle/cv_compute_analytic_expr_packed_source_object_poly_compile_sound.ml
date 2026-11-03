(* ========================================================================== *)
(* Total exact-object execution of valid compiled polynomial expressions.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This theorem supplies the logical witness    *)
(* needed when reflecting a successful ordinary source step.  It is generic *)
(* in the polynomial expression; no case-16594 trace is reconstructed here.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_poly_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_poly_compile_sound = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_poly_program_sound;;

let candle_q_packed_object_poly_run_append = prove
 (`!left right radii center_boxes outer_boxes stack result.
     candle_q_packed_object_poly_run radii center_boxes outer_boxes
       (APPEND left right) stack result <=>
     ?middle.
       candle_q_packed_object_poly_run radii center_boxes outer_boxes
         left stack middle /\
       candle_q_packed_object_poly_run radii center_boxes outer_boxes
         right middle result`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [APPEND; candle_q_packed_object_poly_run_def] THEN
  MESON_TAC[]);;

let candle_q_packed_object_poly_compile_run_exists = prove
 (`!polynomial center_boxes outer_boxes radii stack.
     candle_poly_valid_dim 6 polynomial
     ==>
     ?result.
       candle_q_packed_object_poly_run radii center_boxes outer_boxes
         (candle_poly_compile polynomial) stack (CONS result stack)`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `n:num`; `d:num`] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC
      [candle_poly_compile_def; candle_q_packed_object_poly_run_def;
       candle_q_packed_object_poly_step_def] THEN
    MESON_TAC[];
    X_GEN_TAC `variable:num` THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_TAC THEN
    REWRITE_TAC
      [candle_poly_compile_def; candle_q_packed_object_poly_run_def;
       candle_q_packed_object_poly_step_def] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `inner_poly:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "inner_ih") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile inner_poly) stack (CONS inner stack)`
    (X_CHOOSE_THEN `inner:candle_q_packed_object_item`
      (LABEL_TAC "inner_run")) THENL
     [USE_THEN "inner_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
        `candle_q_packed_object_source_item_neg radii inner` THEN
      REWRITE_TAC
        [candle_poly_compile_def; candle_q_packed_object_poly_run_append] THEN
      EXISTS_TAC
        `(CONS inner stack):(candle_q_packed_object_item)list` THEN
      CONJ_TAC THENL
       [USE_THEN "inner_run" ACCEPT_TAC;
        REWRITE_TAC
          [candle_q_packed_object_poly_run_def;
           candle_q_packed_object_poly_step_def] THEN
        MESON_TAC[]]];
    MAP_EVERY X_GEN_TAC
      [`left_poly:candle_poly_expr`; `right_poly:candle_poly_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "left_ih") (LABEL_TAC "right_ih")) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `?left.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile left_poly) stack (CONS left stack)`
    (X_CHOOSE_THEN `left:candle_q_packed_object_item`
      (LABEL_TAC "left_run")) THENL
     [USE_THEN "left_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile right_poly) (CONS left stack)
          (CONS right (CONS left stack))`
    (X_CHOOSE_THEN `right:candle_q_packed_object_item`
      (LABEL_TAC "right_run")) THENL
     [USE_THEN "right_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
        `candle_q_packed_object_source_item_add radii left right` THEN
      REWRITE_TAC
        [candle_poly_compile_def; candle_q_packed_object_poly_run_append] THEN
      EXISTS_TAC
        `(CONS left stack):(candle_q_packed_object_item)list` THEN
      CONJ_TAC THENL
       [USE_THEN "left_run" ACCEPT_TAC;
        EXISTS_TAC
          `(CONS right (CONS left stack)):
             (candle_q_packed_object_item)list` THEN
        CONJ_TAC THENL
         [USE_THEN "right_run" ACCEPT_TAC;
          REWRITE_TAC
            [candle_q_packed_object_poly_run_def;
             candle_q_packed_object_poly_step_def] THEN
          MESON_TAC[]]]];
    MAP_EVERY X_GEN_TAC
      [`left_poly:candle_poly_expr`; `right_poly:candle_poly_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "left_ih") (LABEL_TAC "right_ih")) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `?left.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile left_poly) stack (CONS left stack)`
    (X_CHOOSE_THEN `left:candle_q_packed_object_item`
      (LABEL_TAC "left_run")) THENL
     [USE_THEN "left_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile right_poly) (CONS left stack)
          (CONS right (CONS left stack))`
    (X_CHOOSE_THEN `right:candle_q_packed_object_item`
      (LABEL_TAC "right_run")) THENL
     [USE_THEN "right_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
        `candle_q_packed_object_source_item_mul radii left right` THEN
      REWRITE_TAC
        [candle_poly_compile_def; candle_q_packed_object_poly_run_append] THEN
      EXISTS_TAC
        `(CONS left stack):(candle_q_packed_object_item)list` THEN
      CONJ_TAC THENL
       [USE_THEN "left_run" ACCEPT_TAC;
        EXISTS_TAC
          `(CONS right (CONS left stack)):
             (candle_q_packed_object_item)list` THEN
        CONJ_TAC THENL
         [USE_THEN "right_run" ACCEPT_TAC;
          REWRITE_TAC
            [candle_q_packed_object_poly_run_def;
             candle_q_packed_object_poly_step_def] THEN
          MESON_TAC[]]]];
    X_GEN_TAC `inner_poly:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "inner_ih") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_packed_object_poly_run radii center_boxes outer_boxes
          (candle_poly_compile inner_poly) stack (CONS inner stack)`
    (X_CHOOSE_THEN `inner:candle_q_packed_object_item`
      (LABEL_TAC "inner_run")) THENL
     [USE_THEN "inner_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
        `candle_q_packed_object_source_item_mul radii inner inner` THEN
      REWRITE_TAC
        [candle_poly_compile_def; candle_q_packed_object_poly_run_append] THEN
      EXISTS_TAC
        `(CONS inner stack):(candle_q_packed_object_item)list` THEN
      CONJ_TAC THENL
       [USE_THEN "inner_run" ACCEPT_TAC;
        REWRITE_TAC
          [candle_q_packed_object_poly_run_def;
           candle_q_packed_object_poly_step_def] THEN
        MESON_TAC[]]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_poly_run_append;
     candle_q_packed_object_poly_compile_run_exists] then
  failwith "packed object polynomial compile sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_POLY_COMPILE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
