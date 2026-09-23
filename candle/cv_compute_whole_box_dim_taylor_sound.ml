(* ========================================================================== *)
(* Semantic list invariants for the dimension-generic Taylor checker.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These theorems connect the checker's derived  *)
(* center and radius vectors to the real box used by the analytic bridge.     *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_whole_box_jet.ml";;

module Candle_cv_whole_box_dim_taylor_sound = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;

let candle_q_dim_real_zero = prove
 (`candle_q_real candle_q_zero = &0`,
  REWRITE_TAC[candle_q_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_center_environment_list_contains = prove
 (`!boxes.
     candle_q_stack_contains
       (candle_q_center_environment_list boxes)
       (MAP (\i. candle_q_real (candle_q_midpoint i)) boxes)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_center_environment_list_def; MAP;
                  candle_q_stack_contains_def;
                  candle_q_midpoint_point_contains]);;

let candle_q_center_environment_list_length = prove
 (`!boxes.
     LENGTH (candle_q_center_environment_list boxes) = LENGTH boxes`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_center_environment_list_def; LENGTH]);;

let candle_q_radius_list_length = prove
 (`!boxes. LENGTH (candle_q_radius_list boxes) = LENGTH boxes`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_radius_list_def; LENGTH]);;

let candle_q_radius_list_nonnegative = prove
 (`!boxes.
     candle_q_box_valid_list boxes
     ==>
     ALL (\r. &0 <= candle_q_real r) (candle_q_radius_list boxes)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_box_valid_list_def;
                candle_q_radius_list_def; ALL];
    REWRITE_TAC[candle_q_box_valid_list_def;
                candle_q_radius_list_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_box_radius_nonnegative THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_q_box_midpoint_radius = prove
 (`!i.
     candle_q_le (FST i) (SND i)
     ==>
     candle_q_real (FST i) <= candle_q_real (candle_q_midpoint i) /\
     candle_q_real (candle_q_midpoint i) <= candle_q_real (SND i) /\
     max
       (candle_q_real (candle_q_midpoint i) - candle_q_real (FST i))
       (candle_q_real (SND i) - candle_q_real (candle_q_midpoint i))
     <= candle_q_real (candle_q_radius i)`,
  REWRITE_TAC[candle_q_le_real; candle_q_midpoint_real;
              candle_q_radius_real] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* The reflected dot accumulator bounds the corresponding real first-order  *)
(* Taylor sum.  The length premise is already enforced by the source-derived *)
(* checker input contract; interval containment supplies each absolute bound. *)

let candle_q_dot_abs_upper_sound = prove
 (`!radii values intervals.
     ALL (\r. &0 <= candle_q_real r) radii /\
     candle_q_stack_contains intervals values /\
     LENGTH radii = LENGTH values
     ==>
     ITLIST2
       (\r y total. candle_q_real r * abs y + total)
       radii values (&0)
     <= candle_q_real (candle_q_dot_abs_upper radii intervals)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    MP_TAC
     (ISPEC
       `intervals:(((num#num)#num)#((num#num)#num))list`
       list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL; candle_q_stack_contains_def; LENGTH;
                candle_q_dot_abs_upper_def; ITLIST2_DEF;
                candle_q_dim_real_zero; REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "radii_ih") THEN
    MAP_EVERY X_GEN_TAC
     [`values:real list`;
      `intervals:(((num#num)#num)#((num#num)#num))list`] THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN `y:real`
         (X_CHOOSE_THEN `ys:real list` SUBST_ALL_TAC))) THEN
    MP_TAC
     (ISPEC
       `intervals:(((num#num)#num)#((num#num)#num))list`
       list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN
         `i:((num#num)#num)#((num#num)#num)`
         (X_CHOOSE_THEN
           `is:(((num#num)#num)#((num#num)#num))list`
           SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[ALL; candle_q_stack_contains_def; LENGTH;
                    candle_q_dot_abs_upper_def; ITLIST2_DEF; HD; TL;
                    candle_q_real_add; candle_q_real_mul] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    SUBGOAL_THEN
     `ITLIST2
        (\r y total. candle_q_real r * abs y + total)
        t ys (&0)
      <= candle_q_real (candle_q_dot_abs_upper t is)`
     ASSUME_TAC THENL
     [USE_THEN "radii_ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs y <= candle_q_real (candle_q_abs_upper i)`
     ASSUME_TAC THENL
     [MATCH_MP_TAC candle_q_abs_upper_sound THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_real h * abs y <=
      candle_q_real h * candle_q_real (candle_q_abs_upper i)`
     ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

(* The outer reflected accumulator likewise bounds a complete real Hessian *)
(* double sum.  This lemma is dimension-independent; the source compiler     *)
(* supplies the square-matrix shape premises once for every expression.      *)

let candle_q_weighted_rows_abs_upper_sound = prove
 (`!radii weights value_rows interval_rows.
     ALL (\r. &0 <= candle_q_real r) radii /\
     ALL (\w. &0 <= candle_q_real w) weights /\
     ALL2 candle_q_stack_contains interval_rows value_rows /\
     LENGTH weights = LENGTH value_rows /\
     ALL (\values. LENGTH radii = LENGTH values) value_rows
     ==>
     ITLIST2
       (\w values total.
          candle_q_real w *
          ITLIST2
            (\r y subtotal. candle_q_real r * abs y + subtotal)
            radii values (&0) + total)
       weights value_rows (&0)
     <= candle_q_real
          (candle_q_weighted_rows_abs_upper
            radii weights interval_rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `value_rows:(real list)list` list_CASES) THEN
    MP_TAC
     (ISPEC
       `interval_rows:((((num#num)#num)#((num#num)#num))list)list`
       list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL; ALL2; LENGTH;
                candle_q_weighted_rows_abs_upper_def; ITLIST2_DEF;
                candle_q_dim_real_zero; REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "weights_ih") THEN
    MAP_EVERY X_GEN_TAC
     [`value_rows:(real list)list`;
      `interval_rows:((((num#num)#num)#((num#num)#num))list)list`] THEN
    MP_TAC (ISPEC `value_rows:(real list)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN `values:real list`
         (X_CHOOSE_THEN `value_tail:(real list)list` SUBST_ALL_TAC))) THEN
    MP_TAC
     (ISPEC
       `interval_rows:((((num#num)#num)#((num#num)#num))list)list`
       list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN
         `intervals:(((num#num)#num)#((num#num)#num))list`
         (X_CHOOSE_THEN
           `interval_tail:((((num#num)#num)#((num#num)#num))list)list`
           SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[ALL; ALL2; LENGTH;
                    candle_q_weighted_rows_abs_upper_def; ITLIST2_DEF;
                    HD; TL; candle_q_real_add; candle_q_real_mul] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    SUBGOAL_THEN
     `ITLIST2
        (\r y subtotal. candle_q_real r * abs y + subtotal)
        radii values (&0)
      <= candle_q_real (candle_q_dot_abs_upper radii intervals)`
     (LABEL_TAC "row_bound") THENL
     [MATCH_MP_TAC candle_q_dot_abs_upper_sound THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ITLIST2
        (\w values total.
           candle_q_real w *
           ITLIST2
             (\r y subtotal. candle_q_real r * abs y + subtotal)
             radii values (&0) + total)
        t value_tail (&0)
      <= candle_q_real
           (candle_q_weighted_rows_abs_upper
             radii t interval_tail)`
     (LABEL_TAC "tail_bound") THENL
     [USE_THEN "weights_ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_real h *
        ITLIST2
          (\r y subtotal. candle_q_real r * abs y + subtotal)
          radii values (&0)
      <= candle_q_real h *
         candle_q_real (candle_q_dot_abs_upper radii intervals)`
     ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

end;;
