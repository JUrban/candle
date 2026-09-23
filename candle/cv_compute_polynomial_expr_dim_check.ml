(* ========================================================================== *)
(* Source-authenticated dimension-generic reflected polynomial checker.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical checker receives no independent *)
(* gradient or Hessian authority: both program collections are derived in HOL *)
(* from the same expression AST whose denotation is connected to the source. *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_polynomial_expr_diff.ml";;

module Candle_cv_polynomial_expr_dim_check = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_whole_box_dim_taylor;;

let candle_q_rows_width_all = prove
  (`!width rows.
     candle_q_rows_width width rows <=>
     ALL (\row. LENGTH row = width) rows`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_rows_width_def; ALL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[candle_q_rows_width_def; ALL]]);;

let candle_q_box_valid_list_all = prove
 (`!boxes.
     candle_q_box_valid_list boxes <=>
     ALL (\box. candle_q_le (FST box) (SND box)) boxes`,
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_box_valid_list_def; ALL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[candle_q_box_valid_list_def; ALL]]);;

let candle_q_box_valid_list_el = prove
 (`!boxes i.
     candle_q_box_valid_list boxes /\ i < LENGTH boxes
     ==> candle_q_le (FST (EL i boxes)) (SND (EL i boxes))`,
  REWRITE_TAC[candle_q_box_valid_list_all; GSYM ALL_EL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "all_boxes") (LABEL_TAC "in_range")) THEN
  USE_THEN "all_boxes" (fun th -> MATCH_MP_TAC (SPEC `i:num` th)) THEN
  ASM_REWRITE_TAC[]);;

let candle_poly_hessian_programs_rows_width = prove
 (`!nvars e.
     candle_q_rows_width nvars
       (candle_poly_hessian_programs nvars e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_rows_width_all; GSYM ALL_EL;
              candle_poly_hessian_programs_length] THEN
  ASM_SIMP_TAC[candle_poly_hessian_programs_row_length]);;

let candle_poly_derived_inputs_valid = prove
 (`!nvars e boxes.
     LENGTH boxes = nvars
     ==>
     candle_q_dim_inputs_valid
       (candle_poly_gradient_programs nvars e)
       (candle_poly_hessian_programs nvars e)
       boxes`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_inputs_valid_def;
                  candle_poly_gradient_programs_length;
                  candle_poly_hessian_programs_length;
                  candle_poly_hessian_programs_rows_width]);;

let candle_poly_derived_inputs_valid_length = prove
 (`!e boxes.
     candle_q_dim_inputs_valid
       (candle_poly_gradient_programs (LENGTH boxes) e)
       (candle_poly_hessian_programs (LENGTH boxes) e)
       boxes`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_poly_derived_inputs_valid THEN
  REWRITE_TAC[]);;

let candle_poly_dim_whole_box_accept_def = new_definition
 `candle_poly_dim_whole_box_accept e boxes <=>
    candle_poly_valid_dim (LENGTH boxes) e /\
    candle_q_dim_whole_box_accept
      (candle_poly_compile e)
      (candle_poly_gradient_programs (LENGTH boxes) e)
      (candle_poly_hessian_programs (LENGTH boxes) e)
      boxes`;;

(* This form is the numerical premise used by the eventual language-wide     *)
(* analytic soundness theorem.  It exposes only [e] and [boxes]; the value,   *)
(* gradient, and Hessian programs cannot be substituted independently.       *)

let candle_poly_dim_whole_box_accept_components = prove
 (`!e boxes.
     candle_poly_dim_whole_box_accept e boxes
     ==>
     candle_poly_valid_dim (LENGTH boxes) e /\
     candle_q_dim_inputs_valid
       (candle_poly_gradient_programs (LENGTH boxes) e)
       (candle_poly_hessian_programs (LENGTH boxes) e)
       boxes /\
     candle_q_box_valid_list boxes /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_whole_box_upper
          (candle_poly_compile e)
          (candle_poly_gradient_programs (LENGTH boxes) e)
          (candle_poly_hessian_programs (LENGTH boxes) e)
          boxes))`,
  REWRITE_TAC[candle_poly_dim_whole_box_accept_def;
              candle_q_dim_whole_box_accept_def]);;

end;;
