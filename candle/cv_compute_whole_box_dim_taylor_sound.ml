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
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;

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

end;;
