(* ========================================================================== *)
(* Exact packed-object Taylor gradient completion.                           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast object route completes each center  *)
(* gradient row by adding one half of twice its absolute Hessian variation.  *)
(* This file proves that the faithful unnormalised object formula has the    *)
(* same real endpoints as the ordinary exact Taylor gradient formula and    *)
(* therefore encloses every first partial on the source cell.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_exact_gradient_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_hessian_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_exact_gradient_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_object_gradient_row_complete_def = new_definition
 `candle_q_packed_object_gradient_row_complete radii center_entry interval_row =
    let variation = candle_q_dot_abs_upper radii interval_row in
    let error = candle_q_add variation variation in
    let half_error = candle_q_mul error candle_q_half in
    candle_q_interval_add center_entry
      (candle_q_neg half_error,half_error)`;;

let candle_q_packed_object_gradient_rows_complete_def = define
 `(candle_q_packed_object_gradient_rows_complete radii [] interval_rows = []) /\
  (candle_q_packed_object_gradient_rows_complete
     radii (CONS center_entry center_rest) [] = []) /\
  (candle_q_packed_object_gradient_rows_complete
     radii (CONS center_entry center_rest)
       (CONS interval_row interval_rows) =
     CONS
       (candle_q_packed_object_gradient_row_complete
         radii center_entry interval_row)
       (candle_q_packed_object_gradient_rows_complete
         radii center_rest interval_rows))`;;

let candle_q_packed_object_gradient_complete6_def = new_definition
 `candle_q_packed_object_gradient_complete6
      radii center_gradient packed_hessian =
    candle_q_packed_object_gradient_rows_complete radii center_gradient
      (candle_q_packed_hessian6_expand packed_hessian)`;;

let candle_q_packed_object_gradient_row_complete_real = prove
 (`!radii center_entry interval_row.
     candle_q_real
       (FST
         (candle_q_packed_object_gradient_row_complete
           radii center_entry interval_row)) =
     candle_q_real
       (FST
         (candle_q_interval_add_extended center_entry
           (candle_q_symmetric_interval
             (candle_q_dot_abs_upper_extended radii interval_row)))) /\
     candle_q_real
       (SND
         (candle_q_packed_object_gradient_row_complete
           radii center_entry interval_row)) =
     candle_q_real
       (SND
         (candle_q_interval_add_extended center_entry
           (candle_q_symmetric_interval
             (candle_q_dot_abs_upper_extended radii interval_row))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_gradient_row_complete_def;
              candle_q_interval_add_def;
              candle_q_interval_add_extended_def;
              candle_q_symmetric_interval_def;
              candle_q_dot_abs_upper_extended_real;
              candle_q_real_add_normalized_extended;
              candle_q_real_add; candle_q_real_mul; candle_q_real_neg;
              candle_q_real_half; FST; SND; LET_DEF; LET_END_DEF] THEN
  REAL_ARITH_TAC);;

let candle_q_packed_object_gradient_row_complete_contains = prove
 (`!radii center_entry interval_row x.
     candle_q_interval_contains
       (candle_q_interval_add_extended center_entry
         (candle_q_symmetric_interval
           (candle_q_dot_abs_upper_extended radii interval_row))) x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_gradient_row_complete
         radii center_entry interval_row) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`radii:((num#num)#num)list`;
       `center_entry:((num#num)#num)#((num#num)#num)`;
       `interval_row:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_object_gradient_row_complete_real) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_q_packed_object_gradient_rows_complete_contains = prove
 (`!radii center_gradient interval_rows values.
     candle_q_stack_contains
       (candle_q_dim_taylor_model_gradient_bounds
         radii center_gradient interval_rows) values
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_gradient_rows_complete
         radii center_gradient interval_rows) values`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_dim_taylor_model_gradient_bounds_def;
                candle_q_packed_object_gradient_rows_complete_def;
                candle_q_stack_contains_def];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    X_GEN_TAC
      `interval_rows:
         ((((num#num)#num)#((num#num)#num))list)list` THEN
    MP_TAC
      (ISPEC
        `interval_rows:
           ((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    X_GEN_TAC `values:real list` THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_dim_taylor_model_gradient_bounds_def;
                candle_q_packed_object_gradient_rows_complete_def;
                candle_q_stack_contains_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_gradient_row_complete_contains THEN
      ASM_REWRITE_TAC[];
      USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_gradient_rows_complete_sound = prove
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
       (candle_q_packed_object_gradient_rows_complete
         radii center_gradient hessian)
       (list_of_seq
         (\di. partial (di + 1) f p)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_gradient_rows_complete_contains THEN
  MATCH_MP_TAC
    (ISPECL
      [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
       `radii:((num#num)#num)list`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `hessian:
          ((((num#num)#num)#((num#num)#num))list)list`;
       `p:real^N`]
      candle_q_exact_taylor_gradient_bounds_unrounded_contains) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_gradient_complete6_sound = prove
 (`!(f:real^6->real) (lower:real^6) (upper:real^6) (y:real^6)
       radii center_gradient packed_hessian (p:real^6).
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_q_stack_contains center_gradient
       (list_of_seq (\di. partial (di + 1) f y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains
             (candle_q_packed_hessian6_expand packed_hessian)
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z) 6) 6)) /\
     p IN interval [lower,upper]
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_gradient_complete6
         radii center_gradient packed_hessian)
       (list_of_seq (\di. partial (di + 1) f p) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_gradient_complete6_def] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_packed_hessian6_expand packed_hessian) = 6`
   ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_packed_hessian6_expand_def; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE [`:6`,`:N`]
        candle_q_packed_object_gradient_rows_complete_sound)) THEN
  MAP_EVERY EXISTS_TAC
    [`lower:real^6`; `upper:real^6`; `y:real^6`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[candle_q_packed_hessian6_expand_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_gradient_row_complete_real;
     candle_q_packed_object_gradient_row_complete_contains;
     candle_q_packed_object_gradient_rows_complete_contains;
     candle_q_packed_object_gradient_rows_complete_sound;
     candle_q_packed_object_gradient_complete6_sound] then
  failwith "packed object gradient soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_GRADIENT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
