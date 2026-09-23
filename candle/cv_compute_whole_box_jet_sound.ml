(* ========================================================================== *)
(* Generic soundness handoff for the reflected whole-box jet checker.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file deliberately assumes only the       *)
(* analytic Taylor contract.  The language-wide calculus bridge establishes  *)
(* that contract once for every valid source expression; this theorem then    *)
(* turns any accepted reflected computation into the original pointwise      *)
(* inequality without rebuilding intermediate arithmetic theorems.           *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_jet.ml";;

module Candle_cv_whole_box_jet_sound = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_jet;;

let candle_q_real_zero = prove
 (`candle_q_real candle_q_zero = &0`,
  REWRITE_TAC[candle_q_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Pure real monotonicity for the exact two-coordinate Taylor expression. *)

let candle_real_taylor_upper_mono = prove
 (`!dx dy rx ry f0 fx fy fxx fxy fyy
     bf bfx bfy bfxx bfxy bfyy.
     &0 <= dx /\ dx <= rx /\ &0 <= dy /\ dy <= ry /\
     f0 <= bf /\
     abs fx <= bfx /\ abs fy <= bfy /\
     abs fxx <= bfxx /\ abs fxy <= bfxy /\ abs fyy <= bfyy
     ==>
     f0 + dx * abs fx + dy * abs fy +
       inv (&2) *
       (dx * (dx * abs fxx + &2 * dy * abs fxy) +
        dy * (dy * abs fyy))
     <=
     bf +
       ((rx * bfx + ry * bfy) +
        inv (&2) *
        (rx * (rx * bfxx + &2 * ry * bfxy) +
         ry * (ry * bfyy)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= bfx /\ &0 <= bfy /\ &0 <= bfxx /\
                &0 <= bfxy /\ &0 <= bfyy`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs fx` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs fy` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs fxx` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs fxy` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs fyy` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dx * abs fx <= rx * bfx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy * abs fy <= ry * bfy` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `dx * abs fxx <= rx * bfxx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy * abs fxy <= ry * bfxy` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (dy * abs fxy) <= &2 * (ry * bfxy)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dx * (dx * abs fxx + &2 * dy * abs fxy) <=
    rx * (rx * bfxx + &2 * ry * bfxy)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[REAL_ABS_POS]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy * abs fyy <= ry * bfyy` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy * (dy * abs fyy) <= ry * (ry * bfyy)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv (&2) *
      (dx * (dx * abs fxx + &2 * dy * abs fxy) +
       dy * (dy * abs fyy)) <=
    inv (&2) *
      (rx * (rx * bfxx + &2 * ry * bfxy) +
       ry * (ry * bfyy))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* The numerical checker-to-contract theorem.  All recurring numerical work *)
(* has already happened as reflected data.                                    *)

let candle_q_jet_whole_box_upper_sound = prove
 (`!program ix iy (f:real->real->real).
     candle_q_box_valid ix iy /\
     candle_real_jet_taylor_contract program ix iy f
     ==>
     !x y.
       candle_q_interval_contains ix x /\
       candle_q_interval_contains iy y
       ==> f x y <=
           candle_q_real
             (candle_q_jet_whole_box_upper program ix iy)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_box_valid_def;
              candle_real_jet_taylor_contract_def] THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2
       (LABEL_TAC "ix_valid") (LABEL_TAC "iy_valid"))
     (LABEL_TAC "contract")) THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "x_in") (LABEL_TAC "y_in")) THEN
  USE_THEN "contract"
   (fun contract_th ->
      USE_THEN "x_in"
       (fun x_in_th ->
          USE_THEN "y_in"
           (fun y_in_th ->
              MP_TAC
               (MATCH_MP
                 (SPECL [`x:real`; `y:real`] contract_th)
                 (CONJ x_in_th y_in_th))))) THEN
  DISCH_THEN
   (X_CHOOSE_THEN `u:real`
     (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC
   (SPECL
     [`program:candle_q_instruction list`;
      `candle_q_point_interval
        (candle_q_midpoint
          (ix:((num#num)#num)#((num#num)#num)))`;
      `candle_q_point_interval
        (candle_q_midpoint
          (iy:((num#num)#num)#((num#num)#num)))`;
      `candle_q_real (candle_q_midpoint ix)`;
      `candle_q_real (candle_q_midpoint iy)`]
     candle_q_jet_program_contains) THEN
  REWRITE_TAC[candle_q_midpoint_point_contains] THEN
  DISCH_THEN (MP_TAC o REWRITE_RULE[candle_q_jet_contains_def]) THEN
  STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`program:candle_q_instruction list`;
      `ix:((num#num)#num)#((num#num)#num)`;
      `iy:((num#num)#num)#((num#num)#num)`;
      `u:real`; `v:real`]
     candle_q_jet_program_contains) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o REWRITE_RULE[candle_q_jet_contains_def]) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `candle_real_jet_f
      (candle_real_jet_program
        (candle_q_real (candle_q_midpoint ix))
        (candle_q_real (candle_q_midpoint iy)) program) +
    abs (x - candle_q_real (candle_q_midpoint ix)) *
      abs (candle_real_jet_fx
        (candle_real_jet_program
          (candle_q_real (candle_q_midpoint ix))
          (candle_q_real (candle_q_midpoint iy)) program)) +
    abs (y - candle_q_real (candle_q_midpoint iy)) *
      abs (candle_real_jet_fy
        (candle_real_jet_program
          (candle_q_real (candle_q_midpoint ix))
          (candle_q_real (candle_q_midpoint iy)) program)) +
    inv (&2) *
      (abs (x - candle_q_real (candle_q_midpoint ix)) *
         (abs (x - candle_q_real (candle_q_midpoint ix)) *
            abs (candle_real_jet_fxx
              (candle_real_jet_program u v program)) +
          &2 * abs (y - candle_q_real (candle_q_midpoint iy)) *
            abs (candle_real_jet_fxy
              (candle_real_jet_program u v program))) +
       abs (y - candle_q_real (candle_q_midpoint iy)) *
         (abs (y - candle_q_real (candle_q_midpoint iy)) *
            abs (candle_real_jet_fyy
              (candle_real_jet_program u v program))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_jet_whole_box_upper_def;
                candle_q_taylor_upper_def; candle_q_real_add;
                candle_q_real_mul; candle_q_real_half;
                candle_q_real_two] THEN
    MATCH_MP_TAC candle_real_taylor_upper_mono THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC candle_q_box_deviation THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC candle_q_box_deviation THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[candle_q_interval_contains_def];
      MATCH_MP_TAC candle_q_abs_upper_sound THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_abs_upper_sound THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_abs_upper_sound THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_abs_upper_sound THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[candle_q_abs_upper_sound]]]);;

let candle_q_jet_whole_box_accept_sound = prove
 (`!program ix iy (f:real->real->real).
     candle_real_jet_taylor_contract program ix iy f /\
     candle_q_jet_whole_box_accept program ix iy
     ==>
     !x y.
       candle_q_interval_contains ix x /\
       candle_q_interval_contains iy y
       ==> f x y < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_whole_box_accept_def] THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (LABEL_TAC "contract")
     (CONJUNCTS_THEN2
       (LABEL_TAC "box_valid") (LABEL_TAC "negative"))) THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  DISCH_THEN (LABEL_TAC "point_in_box") THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `candle_q_real (candle_q_jet_whole_box_upper program ix iy)` THEN
  CONJ_TAC THENL
   [MP_TAC
     (SPECL
       [`program:candle_q_instruction list`;
        `ix:((num#num)#num)#((num#num)#num)`;
        `iy:((num#num)#num)#((num#num)#num)`;
        `f:real->real->real`]
       candle_q_jet_whole_box_upper_sound) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "negative" MP_TAC THEN
    REWRITE_TAC[candle_q_le_real; candle_q_real_zero; REAL_NOT_LE]]);;

end;;
