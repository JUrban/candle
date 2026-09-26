(* ========================================================================== *)
(* Analytic invariant lift for reflected signed fixed-scale Taylor models.   *)
(*                                                                            *)
(* The numerical backend computes only fixed-scale data.  This file connects *)
(* its completed result to the dimension-generic analytic interface, outside *)
(* the hot computation path.                                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_complete_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_invariant = struct

open Multivariate_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_complete_sound;;

let candle_fs_list_real_vector_def = new_definition
 `candle_fs_list_real_vector zs : real^N =
    lambda i. candle_fs_real (EL (i - 1) zs)`;;

let candle_fs_list_real_vector_component = prove
 (`!zs i.
     1 <= i /\ i <= dimindex (:N)
     ==> (candle_fs_list_real_vector zs : real^N)$i =
         candle_fs_real (EL (i - 1) zs)`,
  SIMP_TAC[candle_fs_list_real_vector_def; LAMBDA_BETA]);;

(* The polynomial backend receives the already outward-rounded rational     *)
(* radii and drops only their fixed denominator before entering the hot     *)
(* signed-integer path.  Record once that this changes representation, not  *)
(* the real cell used by the Taylor theorem.                                 *)

let candle_fs_list_of_q_length = prove
 (`!items. LENGTH (candle_fs_list_of_q items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_list_of_q_def; LENGTH]);;

let candle_fs_list_of_q_map = prove
 (`!items. candle_fs_list_of_q items = MAP FST items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_list_of_q_def; MAP]);;

let candle_fs_fixed_round_upper_real = prove
 (`!q.
     candle_fs_real (FST (candle_q_fixed_round_upper q)) =
     candle_q_real (candle_q_fixed_round_upper q)`,
  REWRITE_TAC[GSYM candle_fs_of_q_upper_def;
              candle_fs_of_q_upper_real]);;

let candle_fs_rounded_list_map_real = prove
 (`!items.
     MAP candle_fs_real
       (candle_fs_list_of_q
         (candle_q_fixed_list_round_upper items)) =
     MAP candle_q_real (candle_q_fixed_list_round_upper items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_list_round_upper_def;
                  candle_fs_list_of_q_def; MAP;
                  candle_fs_fixed_round_upper_real]);;

let candle_fs_rounded_list_real_vector = prove
 (`!items.
     LENGTH items = dimindex (:N)
     ==>
     (candle_fs_list_real_vector
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper items)) : real^N) =
     candle_q_list_real_vector
       (candle_q_fixed_list_round_upper items)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= i /\ i <= dimindex (:N)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_fs_list_real_vector_component;
               candle_q_list_real_vector_component] THEN
  let list_th = SPEC `items:((num#num)#num)list`
    candle_fs_rounded_list_map_real in
  let el_th = AP_TERM `(\xs:real list. EL (i - 1) xs)` list_th in
  MP_TAC el_th THEN
  ASM_SIMP_TAC[EL_MAP; candle_fs_list_of_q_length;
               candle_q_fixed_list_round_upper_length]);;

let candle_fs_rounded_list_nonnegative = prove
 (`!items.
     ALL (\q. &0 <= candle_q_real q)
       (candle_q_fixed_list_round_upper items)
     ==>
     ALL (\z. &0 <= candle_fs_real z)
       (candle_fs_list_of_q
         (candle_q_fixed_list_round_upper items))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `i < LENGTH (candle_q_fixed_list_round_upper items)`
   ASSUME_TAC THENL
   [UNDISCH_TAC
      `i < LENGTH
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper items))` THEN
    REWRITE_TAC[candle_fs_list_of_q_length];
    ALL_TAC] THEN
  let list_th = SPEC `items:((num#num)#num)list`
    candle_fs_rounded_list_map_real in
  let el_th = AP_TERM `(\xs:real list. EL i xs)` list_th in
  SUBGOAL_THEN
   `candle_fs_real
      (EL i
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper items))) =
    candle_q_real
      (EL i (candle_q_fixed_list_round_upper items))`
   SUBST1_TAC THENL
   [MP_TAC el_th THEN ASM_SIMP_TAC[EL_MAP]; ALL_TAC] THEN
  MP_TAC (REWRITE_RULE[GSYM ALL_EL]
    (ASSUME
      `ALL (\q. &0 <= candle_q_real q)
        (candle_q_fixed_list_round_upper items)`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_fs_rounded_radii_m_cell_domain = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     m_cell_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_center_vector boxes)
       (candle_fs_list_real_vector
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_radius_list boxes) = dimindex (:N)`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length]; ALL_TAC] THEN
  let vector_th = MATCH_MP
    (ISPEC `candle_q_radius_list boxes`
      candle_fs_rounded_list_real_vector)
    (ASSUME
      `LENGTH (candle_q_radius_list boxes) = dimindex (:N)`) in
  ONCE_REWRITE_TAC[vector_th] THEN
  MATCH_MP_TAC candle_q_fixed_list_round_upper_m_cell_domain THEN
  ASM_REWRITE_TAC[]);;

(* Fixed conversion of source intervals is outward.  This is the center     *)
(* environment bridge used by constants and variables in the postfix proof. *)

let candle_fs_interval_list_of_q_contains = prove
 (`!intervals values.
     candle_q_stack_contains intervals values
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_of_q intervals) values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_stack_contains_def;
                candle_fs_interval_list_of_q_def; ALL2];
    GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_q_stack_contains_def;
                    candle_fs_interval_list_of_q_def; ALL2] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_interval_of_q_sound THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fs_center_environment_contains = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_of_q
         (candle_q_center_environment_list boxes))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
  MATCH_MP_TAC candle_q_center_environment_vector_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_dot_list_real_vector_sum = prove
 (`!radii (g:num->real).
     LENGTH radii = dimindex (:N)
     ==>
     ITLIST2
       (\r y total. candle_fs_real r * abs y + total)
       radii (list_of_seq g (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_fs_list_real_vector radii : real^N)$i *
            abs (g (i - 1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`\r y. candle_fs_real r * abs y`;
       `radii:(num#num)list`;
       `list_of_seq (g:num->real) (dimindex (:N))`]
      candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[candle_fs_list_real_vector_component;
                 EL_LIST_OF_SEQ]]);;

let candle_fs_weighted_rows_list_real_vector_sum = prove
 (`!radii (h:num->num->real).
     LENGTH radii = dimindex (:N)
     ==>
     ITLIST2
       (\w values total.
          candle_fs_real w *
          ITLIST2
            (\r y subtotal. candle_fs_real r * abs y + subtotal)
            radii values (&0) + total)
       radii
       (list_of_seq
         (\di. list_of_seq (h di) (dimindex (:N)))
         (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_fs_list_real_vector radii : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_fs_list_real_vector radii : real^N)$j *
                   abs (h (i - 1) (j - 1))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`\w values.
         candle_fs_real w *
         ITLIST2
           (\r y subtotal. candle_fs_real r * abs y + subtotal)
           radii values (&0)`;
       `radii:(num#num)list`;
       `list_of_seq
         (\di. list_of_seq ((h:num->num->real) di) (dimindex (:N)))
         (dimindex (:N))`]
      candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[candle_fs_list_real_vector_component;
                 EL_LIST_OF_SEQ;
                 candle_fs_dot_list_real_vector_sum]]);;

let candle_fs_complete_m_taylor_error_sound = prove
 (`!f (domain:real^N#real^N) radii hessian.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N))))
     ==>
     m_taylor_error f domain
       (candle_fs_list_real_vector radii)
       (candle_fs_raw_real
         (candle_fs_scale *
           (candle_fs_scale * candle_fs_scale))
         (candle_fs_weighted_rows_abs_upper radii radii hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_fs_list_real_vector radii : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_fs_list_real_vector radii : real^N)$j *
                  abs (partial2 j i (f:real^N->real) (z:real^N)))) =
    sum (1..dimindex (:N))
      (\i. (candle_fs_list_real_vector radii : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_fs_list_real_vector radii : real^N)$j *
                  abs
                    (partial2 ((j - 1) + 1) ((i - 1) + 1)
                      f z)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  let sum_th =
    MATCH_MP
      (ISPECL
        [`radii:(num#num)list`;
         `(\di dj. partial2 (dj + 1) (di + 1)
            (f:real^N->real) (z:real^N)):num->num->real`]
        candle_fs_weighted_rows_list_real_vector_sum)
      (ASSUME `LENGTH (radii:(num#num)list) = dimindex (:N)`) in
  ONCE_REWRITE_TAC[GSYM (BETA_RULE sum_th)] THEN
  MATCH_MP_TAC candle_fs_weighted_rows_abs_upper_sound THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]);;

let candle_fs_complete_m_taylor_partial_error_sound = prove
 (`!f i (domain:real^N#real^N) radii interval_row.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 candle_fs_interval_contains interval_row
             (list_of_seq
               (\dj. partial2 (dj + 1) i f z)
               (dimindex (:N))))
     ==>
     m_taylor_partial_error f i domain
       (candle_fs_list_real_vector radii)
       (candle_fs_raw_real
         (candle_fs_scale * candle_fs_scale)
         (candle_fs_dot_abs_upper radii interval_row))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[m_taylor_partial_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\j. (candle_fs_list_real_vector radii : real^N)$j *
           abs (partial2 j i (f:real^N->real) (z:real^N))) =
    sum (1..dimindex (:N))
      (\j. (candle_fs_list_real_vector radii : real^N)$j *
           abs (partial2 ((j - 1) + 1) i f z))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  let sum_th =
    MATCH_MP
      (ISPECL
        [`radii:(num#num)list`;
         `(\dj. partial2 (dj + 1) i
            (f:real^N->real) (z:real^N)):num->real`]
        candle_fs_dot_list_real_vector_sum)
      (ASSUME `LENGTH (radii:(num#num)list) = dimindex (:N)`) in
  ONCE_REWRITE_TAC[GSYM (BETA_RULE sum_th)] THEN
  MATCH_MP_TAC candle_fs_dot_abs_upper_sound THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_fs_dot_list_real_vector_sum_shifted = prove
 (`!radii (h:num->real).
     LENGTH radii = dimindex (:N)
     ==>
     ITLIST2
       (\r value total. candle_fs_real r * abs value + total)
       radii
       (list_of_seq (\di. h (di + 1)) (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_fs_list_real_vector radii : real^N)$i * abs (h i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_dot_list_real_vector_sum] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> i - 1 + 1 = i`]);;

let candle_fs_complete_gradient_error_sound = prove
 (`!f (y:real^N) radii gradient.
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N)))
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_fs_list_real_vector radii : real^N)$i *
            abs (partial i f y)) <=
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_dot_abs_upper radii gradient)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM candle_fs_dot_list_real_vector_sum_shifted] THEN
  MATCH_MP_TAC candle_fs_dot_abs_upper_sound THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

let candle_m_bounded_on_int_contains = prove
  (`!(f:real^N->real) (domain:real^N#real^N) lo hi (p:real^N).
     m_bounded_on_int f domain (lo,hi) /\
     p IN interval [domain]
     ==> lo <= f p /\ f p <= hi`,
  REWRITE_TAC[m_bounded_on_int; Interval_arith.interval_arith] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let candle_fs_complete_value_bound_contains = prove
 (`!(f:real^N->real) (domain:real^N#real^N) (y:real^N) radii
       center_value gradient hessian (p:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain domain y (candle_fs_list_real_vector radii) /\
     diff2_domain domain f /\
     candle_fs_interval_contains center_value (f y) /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [FST domain,SND domain]
     ==>
     candle_fs_interval_contains
       (candle_fs_value_bound
         radii center_value gradient hessian)
       (f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `hessian_error =
      candle_fs_raw_real
        (candle_fs_scale *
          (candle_fs_scale * candle_fs_scale))
        (candle_fs_weighted_rows_abs_upper
          radii radii hessian)` THEN
  ABBREV_TAC
   `total_error =
      candle_fs_raw_real
        (candle_fs_two_scale_squared * candle_fs_scale)
        (candle_fs_value_error_raw radii gradient hessian)` THEN
  MATCH_MP_TAC candle_fs_value_bound_contains_error THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_m_bounded_on_int_contains THEN
  (fun ((asl,_) as goal) ->
     let vars =
       itlist
         (fun (_,th) acc -> union (frees (concl th)) acc)
         asl [] in
     let domain_term =
       find
         (fun tm -> is_var tm && fst (dest_var tm) = "domain")
         vars in
     EXISTS_TAC domain_term goal) THEN
  let bounds_th =
    ISPECL
     [`domain:real^N#real^N`;
      `y:real^N`;
      `(candle_fs_list_real_vector radii : real^N)`;
      `f:real^N->real`;
      `hessian_error:real`;
      `candle_fs_real
         (FST (center_value:(num#num)#(num#num)))`;
      `candle_fs_real
         (SND (center_value:(num#num)#(num#num)))`;
      `total_error:real`;
      `candle_fs_real
         (FST (center_value:(num#num)#(num#num))) - total_error`;
      `candle_fs_real
         (SND (center_value:(num#num)#(num#num))) + total_error`]
     m_taylor_bounds in
  (fun ((asl,w) as goal) ->
     let bounds_th = REWRITE_RULE[IMP_IMP] bounds_th in
     let antecedent,_ = dest_imp (concl bounds_th) in
     let _,point_goal = dest_conj w in
     SUBGOAL_THEN antecedent
      (fun antecedent_th ->
         let bounded_th = MATCH_MP bounds_th antecedent_th in
         let _,point_th =
           find
            (fun (_,th) ->
               aconv
                (concl (REWRITE_RULE[PAIR] th))
                point_goal)
            asl in
         let point_th = REWRITE_RULE[PAIR] point_th in
         MATCH_ACCEPT_TAC (CONJ bounded_th point_th)) goal) THEN
  ASM_REWRITE_TAC[candle_fs_interval_contains_def;
                  Interval_arith.interval_arith;
                  REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "hessian_error" THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_complete_m_taylor_error_sound THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM
       (fun th ->
          MATCH_ACCEPT_TAC
           (REWRITE_RULE[candle_fs_interval_contains_def] th))];
    EXPAND_TAC "hessian_error" THEN EXPAND_TAC "total_error" THEN
    REWRITE_TAC[candle_fs_value_error_raw_real; REAL_LE_RADD] THEN
    MATCH_MP_TAC candle_fs_complete_gradient_error_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_gradient_bounds_map2 = prove
 (`!radii gradients rows.
     LENGTH gradients = LENGTH rows
     ==>
     candle_fs_gradient_bounds radii gradients rows =
     MAP2
       (\gradient_interval interval_row.
          candle_fs_gradient_bound radii gradient_interval interval_row)
       gradients rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; candle_fs_gradient_bounds_def; MAP2_DEF] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; candle_fs_gradient_bounds_def;
                  candle_fs_gradient_bound_def;
                  candle_fs_gradient_bound_raw_def;
                  MAP2_DEF; CONS_11] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[HD; TL; SUC_INJ] THEN
      ONCE_REWRITE_TAC[GSYM candle_fs_gradient_bound_raw_def] THEN
      ONCE_REWRITE_TAC[GSYM candle_fs_gradient_bound_def] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let candle_fs_gradient_bounds_el = prove
 (`!radii gradients rows i.
     LENGTH gradients = LENGTH rows /\ i < LENGTH gradients
     ==>
     EL i (candle_fs_gradient_bounds radii gradients rows) =
     candle_fs_gradient_bound radii (EL i gradients) (EL i rows)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_gradient_bounds_map2] THEN
  MATCH_MP_TAC EL_MAP2 THEN ASM_ARITH_TAC);;

let candle_fs_result_complete_domain = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_domain
       (candle_fs_result_complete_rounded radii domain center hessian) =
     domain`,
  REWRITE_TAC[candle_fs_result_complete_rounded_def;
              candle_fs_result_domain_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_center = prove
 (`!radii (domain:bool) center hessian.
     candle_q_dim_taylor_model_result_center
       (candle_fs_result_to_q
         (candle_fs_result_complete_rounded
           radii domain center hessian)) =
     candle_fs_first_to_q center hessian`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_fs_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_fs_result_center_def;
              candle_fs_result_hessian_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_value_bound = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_value_bound
       (candle_fs_result_complete_rounded radii domain center hessian) =
     candle_fs_value_bound radii
       (candle_fs_first_value center)
       (candle_fs_first_gradient center) hessian`,
  REWRITE_TAC[candle_fs_result_value_bound_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_value_bound_def;
              candle_fs_value_bound_raw_def;
              candle_fs_value_error_raw_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_gradient_bounds = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_gradient_bounds
       (candle_fs_result_complete_rounded radii domain center hessian) =
     candle_fs_gradient_bounds radii
       (candle_fs_first_gradient center) hessian`,
  REWRITE_TAC[candle_fs_result_gradient_bounds_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_hessian = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_hessian
       (candle_fs_result_complete_rounded radii domain center hessian) =
     hessian`,
  REWRITE_TAC[candle_fs_result_hessian_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_proxy = prove
 (`!radii (domain:bool) center hessian.
     candle_q_dim_taylor_model_proxy
       (candle_fs_result_to_q
         (candle_fs_result_complete_rounded
           radii domain center hessian)) =
     candle_q_dim_jet_make
       (candle_fs_interval_to_q
         (candle_fs_value_bound radii
           (candle_fs_first_value center)
           (candle_fs_first_gradient center) hessian))
       (candle_fs_interval_list_to_q
         (candle_fs_gradient_bounds radii
           (candle_fs_first_gradient center) hessian))
       (candle_fs_interval_matrix_to_q hessian)`,
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_fs_result_to_q_def;
              candle_fs_result_complete_value_bound;
              candle_fs_result_complete_gradient_bounds;
              candle_fs_result_complete_hessian;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_fs_complete_gradient_bound_contains = prove
 (`!(f:real^N->real) i (domain:real^N#real^N) (y:real^N) radii
       center_interval interval_row (p:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain domain y (candle_fs_list_real_vector radii) /\
     diff2_domain domain f /\
     candle_fs_interval_contains center_interval (partial i f y) /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 candle_fs_interval_contains interval_row
             (list_of_seq
               (\dj. partial2 (dj + 1) i f z)
               (dimindex (:N)))) /\
     p IN interval [FST domain,SND domain]
     ==>
     candle_fs_interval_contains
       (candle_fs_gradient_bound radii center_interval interval_row)
       (partial i f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `partial_error =
      candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
        (candle_fs_dot_abs_upper radii interval_row)` THEN
  MATCH_MP_TAC candle_fs_gradient_bound_contains_error THEN
  MATCH_MP_TAC candle_m_bounded_on_int_contains THEN
  (fun ((asl,_) as goal) ->
     let vars =
       itlist
         (fun (_,th) acc -> union (frees (concl th)) acc)
         asl [] in
     let domain_term =
       find
         (fun tm -> is_var tm && fst (dest_var tm) = "domain")
         vars in
     EXISTS_TAC domain_term goal) THEN
  (fun ((asl,w) as goal) ->
     let bounds_th =
       ISPECL
        [`domain:real^N#real^N`;
         `y:real^N`;
         `(candle_fs_list_real_vector radii : real^N)`;
         `f:real^N->real`;
         `i:num`;
         `partial_error:real`;
         `candle_fs_real
            (FST (center_interval:(num#num)#(num#num)))`;
         `candle_fs_real
            (SND (center_interval:(num#num)#(num#num)))`;
         `candle_fs_real
            (FST (center_interval:(num#num)#(num#num))) - partial_error`;
         `candle_fs_real
            (SND (center_interval:(num#num)#(num#num))) + partial_error`]
        m_taylor_partial_bounds in
     let bounds_th = REWRITE_RULE[IMP_IMP] bounds_th in
     let antecedent,_ = dest_imp (concl bounds_th) in
     let _,point_goal = dest_conj w in
     SUBGOAL_THEN antecedent
      (fun antecedent_th ->
         let bounded_th = MATCH_MP bounds_th antecedent_th in
         let bounded_th =
           REWRITE_RULE
             [SYM
               (ASSUME
                 `candle_fs_raw_real
                    (candle_fs_scale * candle_fs_scale)
                    (candle_fs_dot_abs_upper radii interval_row) =
                  partial_error`)]
             bounded_th in
         let _,point_th =
           find
            (fun (_,th) ->
               aconv
                (concl (REWRITE_RULE[PAIR] th))
                point_goal)
            asl in
         let point_th = REWRITE_RULE[PAIR] point_th in
         MATCH_ACCEPT_TAC (CONJ bounded_th point_th)) goal) THEN
  ASM_REWRITE_TAC[candle_fs_interval_contains_def;
                  Interval_arith.interval_arith; REAL_LE_REFL] THEN
  EXPAND_TAC "partial_error" THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_complete_m_taylor_partial_error_sound THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM
      (fun th ->
         MATCH_ACCEPT_TAC
           (REWRITE_RULE[candle_fs_interval_contains_def] th))]);;

let candle_fs_complete_gradient_bounds_contains = prove
 (`!(f:real^N->real) (domain:real^N#real^N) (y:real^N) radii
       center_gradient hessian (p:real^N).
     LENGTH radii = dimindex (:N) /\
     LENGTH center_gradient = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain domain y (candle_fs_list_real_vector radii) /\
     diff2_domain domain f /\
     ALL2 candle_fs_interval_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [FST domain,SND domain]
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_gradient_bounds radii center_gradient hessian)
       (list_of_seq
         (\di. partial (di + 1) f p)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (fun goal ->
    let center_length =
      ASSUME
       `LENGTH (center_gradient:((num#num)#(num#num))list) =
        dimindex (:N)` in
    let hessian_length =
      ASSUME
       `LENGTH (hessian:(((num#num)#(num#num))list)list) =
        dimindex (:N)` in
    let matching_lengths = TRANS center_length (SYM hessian_length) in
    let result_length =
      MATCH_MP
       (SPECL
         [`radii:(num#num)list`;
          `center_gradient:((num#num)#(num#num))list`;
          `hessian:(((num#num)#(num#num))list)list`]
         candle_fs_gradient_bounds_length)
       matching_lengths in
    let output_length = TRANS result_length center_length in
    let sequence_th =
      MATCH_MP
       (ISPECL
         [`dimindex (:N)`;
          `candle_fs_gradient_bounds radii center_gradient hessian`]
         candle_list_eq_list_of_seq_el)
       output_length in
    ONCE_REWRITE_TAC [sequence_th] goal) THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_fs_gradient_bounds_el] THEN
  MATCH_MP_TAC
   (ISPECL
     [`f:real^N->real`;
      `di + 1`;
      `domain:real^N#real^N`;
      `y:real^N`;
      `radii:(num#num)list`;
      `EL di (center_gradient:((num#num)#(num#num))list)`;
      `EL di (hessian:(((num#num)#(num#num))list)list)`;
      `p:real^N`]
     candle_fs_complete_gradient_bound_contains) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[candle_all2_right_list_of_seq_el];
    REPEAT STRIP_TAC THEN
    (fun ((asl,conclusion) as goal) ->
      let z =
        find
         (fun tm -> is_var tm && fst (dest_var tm) = "z")
         (frees conclusion) in
      let _,universal =
        find
         (fun (_,th) -> is_forall (concl th))
         asl in
      let conditional = REWRITE_RULE[PAIR] (SPEC z universal) in
      let antecedent,_ = dest_imp (concl conditional) in
      let _,z_in =
        find
         (fun (_,th) -> aconv (concl th) antecedent)
         asl in
      let hessian_contains = MATCH_MP conditional z_in in
      let row_contains =
        tryfind
         (fun (_,th) ->
           MATCH_MP candle_all2_right_list_of_seq_el
             (CONJ hessian_contains th))
         asl in
      let row_contains = REWRITE_RULE[] row_contains in
      MATCH_ACCEPT_TAC row_contains goal)]);;

let candle_fs_result_complete_proxy_contains = prove
 (`!(f:real^N->real) (domain:real^N#real^N) (y:real^N) radii
       center hessian (domain_ok:bool) (p:real^N).
     LENGTH radii = dimindex (:N) /\
     LENGTH (candle_fs_first_gradient center) = dimindex (:N) /\
     LENGTH hessian = dimindex (:N) /\
     ALL (\row. LENGTH row = dimindex (:N)) hessian /\
     ALL (\r. &0 <= candle_fs_real r) radii /\
     m_cell_domain domain y (candle_fs_list_real_vector radii) /\
     diff2_domain domain f /\
     candle_fs_interval_contains (candle_fs_first_value center) (f y) /\
     ALL2 candle_fs_interval_contains (candle_fs_first_gradient center)
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [FST domain,SND domain]
       ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [FST domain,SND domain]
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q
           (candle_fs_result_complete_rounded
             radii domain_ok center hessian)))
       (f p)
       (\di. partial (di + 1) f p)
       (\di dj. partial2 (dj + 1) (di + 1) f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_jet_contains_components_of_stacks THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_result_complete_proxy_shape THEN
    REWRITE_TAC[candle_fs_first_to_q_shape] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_result_complete_proxy;
                candle_q_dim_jet_make_def;
                candle_q_dim_jet_f_def; FST; SND;
                candle_fs_interval_to_q_contains] THEN
    MATCH_MP_TAC candle_fs_complete_value_bound_contains THEN
    MAP_EVERY EXISTS_TAC [`domain:real^N#real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_result_complete_proxy;
                candle_q_dim_jet_make_def;
                candle_q_dim_jet_gradient_def; FST; SND;
                candle_fs_interval_list_to_q_contains] THEN
    MATCH_MP_TAC candle_fs_complete_gradient_bounds_contains THEN
    MAP_EVERY EXISTS_TAC [`domain:real^N#real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_result_complete_proxy;
                candle_q_dim_jet_make_def;
                candle_q_dim_jet_hessian_def; FST; SND;
                candle_fs_interval_matrix_to_q_contains] THEN
    FIRST_ASSUM
     (fun th ->
       if is_forall (concl th) then
         MATCH_MP_TAC (SPEC `p:real^N` th)
       else failwith "not a universal assumption") THEN
    ASM_REWRITE_TAC[]]);;

(* Recover list-level containment from the pointwise jet predicate.  The     *)
(* established arithmetic soundness lemmas consume lists, while the public  *)
(* source invariant deliberately exposes only the dimension-generic jet     *)
(* contract.                                                                 *)

let candle_q_dim_jet_components_gradient_contains = prove
 (`!n jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==>
     candle_q_stack_contains
       (candle_q_dim_jet_gradient jet) (list_of_seq gradient n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_gradient jet =
    list_of_seq (\i. candle_q_dim_jet_gradient_at jet i) n`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_gradient_list_of_seq THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_stack_contains_all2;
                candle_all2_list_of_seq] THEN
    ASM_MESON_TAC[candle_q_dim_jet_contains_components_def]]);;

let candle_q_dim_jet_components_hessian_contains = prove
 (`!n jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian jet)
       (list_of_seq (\i. list_of_seq (hessian i) n) n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_hessian jet =
    list_of_seq
      (\i. list_of_seq
        (\j. candle_q_dim_jet_hessian_at jet i j) n)
      n`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_hessian_list_of_seq THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_all2_list_of_seq] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[candle_q_stack_contains_all2;
                candle_all2_list_of_seq] THEN
    ASM_MESON_TAC[candle_q_dim_jet_contains_components_def]]);;

(* Polynomial postfix nodes have no analytic side conditions.  This compact *)
(* invariant states exactly what later Taylor acceptance needs at the center *)
(* and throughout the box, while keeping every intermediate numerical jet   *)
(* behind the fixed-result conversion boundary.                              *)

let candle_fs_result_poly_invariant_def = new_definition
 `candle_fs_result_poly_invariant
      (type_witness:real^N)
      (boxes:(((num#num)#num)#((num#num)#num))list) result e <=>
    candle_fs_result_domain result
    ==>
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_result_center
        (candle_fs_result_to_q result)) /\
    candle_q_dim_jet_contains_components (dimindex (:N))
      (candle_q_dim_taylor_model_result_center
        (candle_fs_result_to_q result))
      (candle_poly_denote_dim e
        (candle_q_box_center_vector boxes : real^N))
      (\di. partial (di + 1) (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N))
      (\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)) /\
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_proxy
        (candle_fs_result_to_q result)) /\
    (!(p:real^N). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_q_dim_jet_contains_components (dimindex (:N))
              (candle_q_dim_taylor_model_proxy
                (candle_fs_result_to_q result))
              (candle_poly_denote_dim e p)
              (\di. partial (di + 1) (candle_poly_denote_dim e) p)
              (\di dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e) p))`;;

let candle_fs_result_complete_poly_invariant = prove
 (`!e boxes center hessian (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q center hessian) /\
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_fs_first_to_q center hessian)
       (candle_poly_denote_dim e
         (candle_q_box_center_vector boxes : real^N))
       (\di. partial (di + 1) (candle_poly_denote_dim e)
         (candle_q_box_center_vector boxes : real^N))
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_poly_denote_dim e)
         (candle_q_box_center_vector boxes : real^N)) /\
     (!(z:real^N). z IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> ALL2 (ALL2 candle_fs_interval_contains) hessian
              (list_of_seq
                (\di. list_of_seq
                  (\dj. partial2 (dj + 1) (di + 1)
                    (candle_poly_denote_dim e) z)
                  (dimindex (:N)))
                (dimindex (:N))))
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_complete_rounded
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         T center hessian) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def;
              candle_fs_result_complete_domain] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_fs_result_complete_center];
    ASM_REWRITE_TAC[candle_fs_result_complete_center];
    MATCH_MP_TAC candle_fs_result_complete_proxy_shape THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_fs_result_complete_proxy_contains THEN
    MAP_EVERY EXISTS_TAC
      [`((candle_q_box_lower_vector boxes : real^N),
         (candle_q_box_upper_vector boxes : real^N))`;
       `(candle_q_box_center_vector boxes : real^N)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_fs_list_of_q_length;
                     candle_q_fixed_list_round_upper_length;
                     candle_q_radius_list_length];
      MP_TAC
        (REWRITE_RULE[candle_fs_first_to_q_shape]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N))
              (candle_fs_first_to_q center hessian)`)) THEN
      MESON_TAC[];
      MP_TAC
        (REWRITE_RULE[candle_fs_first_to_q_shape]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N))
              (candle_fs_first_to_q center hessian)`)) THEN
      MESON_TAC[];
      MP_TAC
        (REWRITE_RULE[candle_fs_first_to_q_shape]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N))
              (candle_fs_first_to_q center hessian)`)) THEN
      MESON_TAC[];
      ASM_MESON_TAC[candle_fs_rounded_list_nonnegative;
                    candle_q_fixed_list_round_upper_nonnegative;
                    candle_q_radius_list_nonnegative];
      ASM_MESON_TAC[candle_fs_rounded_radii_m_cell_domain];
      REWRITE_TAC[diff2_domain] THEN
      ASM_MESON_TAC[diff2c_imp_diff2;
                    candle_poly_denote_dim_diff2c];
      MP_TAC
        (REWRITE_RULE
          [candle_q_dim_jet_contains_components_def;
           candle_fs_first_to_q_def;
           candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
           candle_fs_interval_to_q_contains; FST; SND]
          (ASSUME
            `candle_q_dim_jet_contains_components (dimindex (:N))
              (candle_fs_first_to_q center hessian)
              (candle_poly_denote_dim e
                (candle_q_box_center_vector boxes : real^N))
              (\di. partial (di + 1) (candle_poly_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))
              (\di dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))`)) THEN
      MESON_TAC[];
      (let gradient_th = MATCH_MP
         (ISPECL
           [`dimindex (:N)`;
            `candle_fs_first_to_q center hessian`;
            `candle_poly_denote_dim e
              (candle_q_box_center_vector boxes : real^N)`;
            `(\di. partial (di + 1) (candle_poly_denote_dim e)
              (candle_q_box_center_vector boxes : real^N)):num->real`;
            `(\di dj. partial2 (dj + 1) (di + 1)
              (candle_poly_denote_dim e)
              (candle_q_box_center_vector boxes : real^N)):num->num->real`]
           candle_q_dim_jet_components_gradient_contains)
         (CONJ
           (ASSUME
             `candle_q_dim_jet_shape (dimindex (:N))
               (candle_fs_first_to_q center hessian)`)
           (ASSUME
             `candle_q_dim_jet_contains_components (dimindex (:N))
               (candle_fs_first_to_q center hessian)
               (candle_poly_denote_dim e
                 (candle_q_box_center_vector boxes : real^N))
               (\di. partial (di + 1) (candle_poly_denote_dim e)
                 (candle_q_box_center_vector boxes : real^N))
               (\di dj. partial2 (dj + 1) (di + 1)
                 (candle_poly_denote_dim e)
                 (candle_q_box_center_vector boxes : real^N))`)) in
       ACCEPT_TAC
         (REWRITE_RULE
           [candle_fs_first_to_q_def;
            candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
            candle_fs_interval_list_to_q_contains; FST; SND]
           gradient_th));
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* Structural facts for the constant and variable compiler leaves.  These  *)
(* are proved over the source-shaped fixed lists, so later postfix proofs    *)
(* need no representation-specific reasoning at each leaf.                  *)

let candle_fs_interval_zeros_length = prove
 (`!items. LENGTH (candle_fs_interval_zeros items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_zeros_def; LENGTH]);;

let candle_fs_interval_unit_length = prove
 (`!variable items.
     LENGTH (candle_fs_interval_unit variable items) = LENGTH items`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_unit_def;
                  candle_fs_interval_zeros_length; LENGTH]);;

let candle_fs_interval_list_of_q_length = prove
 (`!items.
     LENGTH (candle_fs_interval_list_of_q items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_list_of_q_def; LENGTH]);;

let candle_fs_interval_lookup_contains = prove
 (`!variable intervals values.
     ALL2 candle_fs_interval_contains intervals values /\
     variable < LENGTH intervals
     ==>
     candle_fs_interval_contains
       (candle_fs_interval_lookup variable intervals)
       (EL variable values)`,
  INDUCT_TAC THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  MP_TAC (ISPEC `values:real list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_fs_interval_lookup_def; ALL2; LENGTH;
                  EL; HD; TL; LT_SUC; CONJUNCT1 LT] THEN
  ASM_MESON_TAC[]);;

let candle_fs_interval_zero_matrix_shape = prove
 (`!(width:((num#num)#(num#num))list)
      (items:((num#num)#(num#num))list).
     LENGTH (candle_fs_interval_zero_matrix width items) = LENGTH items /\
     ALL (\row. LENGTH row = LENGTH width)
       (candle_fs_interval_zero_matrix width items)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_zero_matrix_def; LENGTH; ALL;
                  candle_fs_interval_zeros_length]);;

let candle_fs_interval_zero_matrix_rows_width = prove
 (`!(width:((num#num)#(num#num))list)
      (items:((num#num)#(num#num))list).
     ALL (\row. LENGTH row = LENGTH width)
       (candle_fs_interval_zero_matrix width items)`,
  REPEAT GEN_TAC THEN
  let shape_th = SPECL
   [`width:((num#num)#(num#num))list`;
    `items:((num#num)#(num#num))list`]
   candle_fs_interval_zero_matrix_shape in
  MATCH_ACCEPT_TAC (CONJUNCT2 shape_th));;

let candle_fs_interval_zero_contains = prove
 (`candle_fs_interval_contains candle_fs_interval_zero (&0)`,
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_zero_def; candle_fs_real_def;
              candle_lc_zreal_def; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_interval_one_contains = prove
 (`candle_fs_interval_contains candle_fs_interval_one (&1)`,
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_one_def; candle_fs_real_def;
              candle_lc_zreal_def; FST; SND] THEN
  SUBGOAL_THEN `~(&(candle_fs_scale) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC candle_fs_scale_pos THEN ARITH_TAC;
    ASM_SIMP_TAC[REAL_SUB_RZERO; REAL_DIV_REFL; REAL_LE_REFL]]);;

let candle_fs_interval_zeros_contains = prove
 (`!items.
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_zeros items)
       (list_of_seq (\i. &0) (LENGTH items))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_zeros_def; LENGTH;
                  LIST_OF_SEQ; o_THM; ALL2;
                  candle_fs_interval_zero_contains] THEN
  let zero_shift = prove
   (`((\i:num. (&0:real)) o SUC) = (\i. (&0:real))`,
    REWRITE_TAC[FUN_EQ_THM; o_THM]) in
  ONCE_REWRITE_TAC[zero_shift] THEN ASM_REWRITE_TAC[]);;

let candle_fs_interval_unit_contains = prove
 (`!variable items.
     variable < LENGTH items
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_unit variable items)
       (list_of_seq
         (\i. if i = variable then &1 else &0)
         (LENGTH items))`,
  INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC
     (ISPEC `items:((num#num)#(num#num))list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[LENGTH; CONJUNCT1 LT];
      DISCH_TAC THEN
      REWRITE_TAC[candle_fs_interval_unit_def; LENGTH;
                  LIST_OF_SEQ; o_THM; ALL2;
                  candle_fs_interval_one_contains] THEN
      let zero_shift = prove
       (`((\i:num. if i = 0 then (&1:real) else &0) o SUC =
         (\i. (&0:real)))`,
        REWRITE_TAC[FUN_EQ_THM; o_THM; NOT_SUC]) in
      ONCE_REWRITE_TAC[zero_shift] THEN
      MATCH_ACCEPT_TAC (SPEC
        `t:((num#num)#(num#num))list`
        candle_fs_interval_zeros_contains)];
    GEN_TAC THEN
    MP_TAC
     (ISPEC `items:((num#num)#(num#num))list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[LENGTH; CONJUNCT1 LT];
      DISCH_TAC THEN
      REWRITE_TAC[candle_fs_interval_unit_def; LENGTH;
                  LIST_OF_SEQ; o_THM; ALL2;
                  candle_fs_interval_zero_contains] THEN
      let unit_shift = prove
       (`((\i:num. if i = SUC variable then (&1:real) else &0) o SUC =
         (\i. if i = variable then &1 else &0))`,
        REWRITE_TAC[FUN_EQ_THM; o_THM; SUC_INJ]) in
      ONCE_REWRITE_TAC[unit_shift] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `~(0 = SUC variable)`;
                    candle_fs_interval_zero_contains];
        (fun ((assumptions,_) as goal) ->
           let _,ih =
             find (fun (_,th) -> is_forall (concl th)) assumptions in
           let _,bound =
             find (fun (_,th) -> not (is_forall (concl th)))
               assumptions in
           let bound = REWRITE_RULE[LENGTH; LT_SUC] bound in
           MATCH_ACCEPT_TAC
             (MATCH_MP
               (SPEC `t:((num#num)#(num#num))list` ih)
               bound) goal)]]]);;

let candle_fs_interval_zero_matrix_contains = prove
 (`!(width:((num#num)#(num#num))list)
      (items:((num#num)#(num#num))list).
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_interval_zero_matrix width items)
       (list_of_seq
         (\di:num. list_of_seq (\dj:num. &0) (LENGTH width))
         (LENGTH items))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_zero_matrix_def; LENGTH;
                  LIST_OF_SEQ; o_THM; ALL2;
                  candle_fs_interval_zeros_contains] THEN
  let row_shift = prove
   (`((\di:num. list_of_seq (\dj:num. (&0:real))
         (LENGTH (width:((num#num)#(num#num))list))) o SUC) =
     (\di. list_of_seq (\dj:num. (&0:real))
       (LENGTH (width:((num#num)#(num#num))list)))`,
    REWRITE_TAC[FUN_EQ_THM; o_THM]) in
  ONCE_REWRITE_TAC[row_shift] THEN ASM_REWRITE_TAC[]);;

let candle_fs_result_constant_poly_invariant = prove
 (`!p n d boxes dimensions (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     LENGTH dimensions = dimindex (:N)
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_constant dimensions
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         ((p,n),d))
       (Candle_poly_const p n d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_constant_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_poly_invariant THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_poly_valid_dim_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_to_q_shape;
                candle_fs_first_make_def;
                candle_fs_first_gradient_def; FST; SND;
                candle_fs_interval_zeros_length;
                candle_fs_interval_zero_matrix_shape;
                candle_fs_interval_zero_matrix_rows_width] THEN
    MP_TAC
     (SPECL
       [`dimensions:((num#num)#(num#num))list`;
       `dimensions:((num#num)#(num#num))list`]
       candle_fs_interval_zero_matrix_rows_width) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_jet_contains_components_of_stacks THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_fs_first_to_q_shape;
                  candle_fs_first_make_def;
                  candle_fs_first_gradient_def; FST; SND;
                  candle_fs_interval_zeros_length;
                  candle_fs_interval_zero_matrix_shape;
                  candle_fs_interval_zero_matrix_rows_width] THEN
      MP_TAC
       (SPECL
         [`dimensions:((num#num)#(num#num))list`;
          `dimensions:((num#num)#(num#num))list`]
         candle_fs_interval_zero_matrix_rows_width) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_fs_first_make_def; candle_fs_first_value_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_f_def; FST; SND;
                  candle_fs_interval_to_q_contains;
                  candle_poly_denote_dim_const] THEN
      MATCH_ACCEPT_TAC candle_fs_interval_constant_sound;
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_fs_first_make_def; candle_fs_first_gradient_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_gradient_def; FST; SND;
                  candle_fs_interval_list_to_q_contains;
                  candle_poly_denote_dim_const; partial_const] THEN
      MP_TAC (SPEC `dimensions:((num#num)#(num#num))list`
        candle_fs_interval_zeros_contains) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_hessian_def; FST; SND;
                  candle_fs_interval_matrix_to_q_contains;
                  candle_poly_denote_dim_const; partial2_const] THEN
      MP_TAC
       (SPECL
         [`dimensions:((num#num)#(num#num))list`;
          `dimensions:((num#num)#(num#num))list`]
         candle_fs_interval_zero_matrix_contains) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[candle_poly_denote_dim_const; partial2_const] THEN
    MP_TAC
     (SPECL
       [`dimensions:((num#num)#(num#num))list`;
       `dimensions:((num#num)#(num#num))list`]
       candle_fs_interval_zero_matrix_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_result_variable_poly_invariant = prove
 (`!variable boxes dimensions (type_witness:real^N).
     variable < dimindex (:N) /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     LENGTH dimensions = dimindex (:N) /\
     ALL2 candle_fs_interval_contains dimensions
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_variable dimensions
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         variable)
       (Candle_poly_var variable)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_variable_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_poly_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_poly_valid_dim_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_to_q_shape;
                candle_fs_first_make_def;
                candle_fs_first_gradient_def; FST; SND;
                candle_fs_interval_unit_length;
                candle_fs_interval_zero_matrix_shape] THEN
    MP_TAC
     (SPECL
       [`dimensions:((num#num)#(num#num))list`;
        `dimensions:((num#num)#(num#num))list`]
       candle_fs_interval_zero_matrix_rows_width) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_jet_contains_components_of_stacks THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_fs_first_to_q_shape;
                  candle_fs_first_make_def;
                  candle_fs_first_gradient_def; FST; SND;
                  candle_fs_interval_unit_length;
                  candle_fs_interval_zero_matrix_shape] THEN
      MP_TAC
       (SPECL
         [`dimensions:((num#num)#(num#num))list`;
          `dimensions:((num#num)#(num#num))list`]
         candle_fs_interval_zero_matrix_rows_width) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_fs_first_make_def; candle_fs_first_value_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_f_def; FST; SND;
                  candle_fs_interval_to_q_contains;
                  candle_poly_denote_dim_var] THEN
      SUBGOAL_THEN
       `(candle_q_box_center_vector boxes : real^N)$(variable + 1) =
        EL variable
          (list_of_seq
            (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
            (dimindex (:N)))`
       SUBST1_TAC THENL
       [ASM_SIMP_TAC[EL_LIST_OF_SEQ];
        MATCH_MP_TAC candle_fs_interval_lookup_contains THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_fs_first_make_def; candle_fs_first_gradient_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_gradient_def; FST; SND;
                  candle_fs_interval_list_to_q_contains] THEN
      MP_TAC
       (ISPECL
         [`Candle_poly_var variable`;
          `(candle_q_box_center_vector boxes : real^N)`]
         candle_poly_gradient_flyspeck_partials) THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def] THEN
      DISCH_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[candle_poly_gradient_def; candle_poly_d_list_def] THEN
      SUBGOAL_THEN
       `list_of_seq
          (\di. if variable = di then &1 else &0)
          (dimindex (:N)) =
        list_of_seq
          (\di. if di = variable then &1 else &0)
          (dimindex (:N))`
       SUBST1_TAC THENL
       [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
        X_GEN_TAC `di:num` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[EL_LIST_OF_SEQ; EQ_SYM_EQ];
        MP_TAC
         (SPECL
           [`variable:num`;
            `dimensions:((num#num)#(num#num))list`]
           candle_fs_interval_unit_contains) THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_hessian_def; FST; SND;
                  candle_fs_interval_matrix_to_q_contains] THEN
      MP_TAC
       (ISPECL
         [`Candle_poly_var variable`;
          `(candle_q_box_center_vector boxes : real^N)`]
         candle_poly_hessian_flyspeck_partials) THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def] THEN
      DISCH_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[candle_poly_hessian_def; candle_poly_dd_list_def] THEN
      MP_TAC
       (SPECL
         [`dimensions:((num#num)#(num#num))list`;
          `dimensions:((num#num)#(num#num))list`]
         candle_fs_interval_zero_matrix_contains) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC
     (ISPECL
       [`Candle_poly_var variable`; `z:real^N`]
       candle_poly_hessian_flyspeck_partials) THEN
    ASM_REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[candle_poly_hessian_def; candle_poly_dd_list_def] THEN
    MP_TAC
     (SPECL
       [`dimensions:((num#num)#(num#num))list`;
        `dimensions:((num#num)#(num#num))list`]
       candle_fs_interval_zero_matrix_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_center_dimensions_length = prove
 (`!boxes.
     LENGTH
       (candle_fs_interval_list_of_q
         (candle_q_center_environment_list boxes)) = LENGTH boxes`,
  REWRITE_TAC[candle_fs_interval_list_of_q_length;
              candle_q_center_environment_list_length]);;

let candle_fs_result_constant_center_poly_invariant = prove
 (`!p n d boxes (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_constant
         (candle_fs_interval_list_of_q
           (candle_q_center_environment_list boxes))
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         ((p,n),d))
       (Candle_poly_const p n d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_result_constant_poly_invariant THEN
  ASM_REWRITE_TAC[candle_fs_center_dimensions_length]);;

let candle_fs_result_variable_center_poly_invariant = prove
 (`!variable boxes (type_witness:real^N).
     variable < dimindex (:N) /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_variable
         (candle_fs_interval_list_of_q
           (candle_q_center_environment_list boxes))
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         variable)
       (Candle_poly_var variable)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_result_variable_poly_invariant THEN
  ASM_REWRITE_TAC[candle_fs_center_dimensions_length] THEN
  MATCH_MP_TAC candle_fs_center_environment_contains THEN
  ASM_REWRITE_TAC[]);;

(* Operation closure consumes the invariant through these fixed-data views. *)
(* They expose only the enclosures needed by the next postfix node.          *)

let candle_fs_result_poly_center_shape = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center result)
         (candle_fs_result_hessian result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def;
              candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_poly_center_components = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fs_result_center result)
         (candle_fs_result_hessian result))
       (candle_poly_denote_dim e
         (candle_q_box_center_vector boxes : real^N))
       (\di. partial (di + 1) (candle_poly_denote_dim e)
         (candle_q_box_center_vector boxes : real^N))
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_poly_denote_dim e)
         (candle_q_box_center_vector boxes : real^N))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def;
              candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_poly_center_value_contains = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     candle_fs_interval_contains
       (candle_fs_first_value (candle_fs_result_center result))
       (candle_poly_denote_dim e
         (candle_q_box_center_vector boxes : real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_center_components) THEN
  ASM_REWRITE_TAC[candle_q_dim_jet_contains_components_def;
                  candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                  candle_fs_interval_to_q_contains; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_poly_center_gradient_contains = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient (candle_fs_result_center result))
       (list_of_seq
         (\di. partial (di + 1) (candle_poly_denote_dim e)
           (candle_q_box_center_vector boxes : real^N))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_center_shape)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_center_components)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let center_jet = rand (concl shape_th) in
  let gradient_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      center_jet;
      `candle_poly_denote_dim e
        (candle_q_box_center_vector boxes : real^N)`;
      `(\di. partial (di + 1) (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)):num->real`;
      `(\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)):num->num->real`]
     candle_q_dim_jet_components_gradient_contains)
   (CONJ shape_th components_th) in
  ACCEPT_TAC
   (REWRITE_RULE
     [candle_fs_first_to_q_def;
      candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
      candle_fs_interval_list_to_q_contains; FST; SND]
     gradient_th));;

let candle_fs_result_poly_center_hessian_contains = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian result)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_poly_denote_dim e)
             (candle_q_box_center_vector boxes : real^N))
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_center_shape)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_center_components)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let center_jet = rand (concl shape_th) in
  let hessian_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      center_jet;
      `candle_poly_denote_dim e
        (candle_q_box_center_vector boxes : real^N)`;
      `(\di. partial (di + 1) (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)):num->real`;
      `(\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e)
        (candle_q_box_center_vector boxes : real^N)):num->num->real`]
     candle_q_dim_jet_components_hessian_contains)
   (CONJ shape_th components_th) in
  ACCEPT_TAC
   (REWRITE_RULE
     [candle_fs_first_to_q_def;
      candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
      candle_fs_interval_matrix_to_q_contains; FST; SND]
     hessian_th));;

let candle_fs_result_poly_proxy_shape = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def] THEN
  MESON_TAC[]);;

let candle_fs_result_poly_proxy_components = prove
 (`!e boxes result (type_witness:real^N) (p:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q result))
       (candle_poly_denote_dim e p)
       (\di. partial (di + 1) (candle_poly_denote_dim e) p)
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_poly_denote_dim e) p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def] THEN
  MESON_TAC[]);;

let candle_fs_result_proxy_to_q_shape = prove
 (`!n
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list).
     candle_q_dim_jet_shape n
       (candle_q_dim_taylor_model_proxy
         (candle_fs_result_to_q result)) <=>
     LENGTH (candle_fs_result_gradient_bounds result) = n /\
     LENGTH (candle_fs_result_hessian result) = n /\
     ALL (\row. LENGTH row = n) (candle_fs_result_hessian result)`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_fs_interval_list_to_q_length;
              candle_fs_interval_matrix_to_q_shape;
              FST; SND]);;

let candle_fs_result_poly_proxy_data_shape = prove
 (`!e boxes result (type_witness:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result
     ==>
     LENGTH (candle_fs_result_gradient_bounds result) = dimindex (:N) /\
     LENGTH (candle_fs_result_hessian result) = dimindex (:N) /\
     ALL (\row. LENGTH row = dimindex (:N))
       (candle_fs_result_hessian result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_proxy_shape) THEN
  ASM_REWRITE_TAC[candle_fs_result_proxy_to_q_shape]);;

let candle_fs_result_poly_proxy_value_contains = prove
 (`!e boxes result (type_witness:real^N) (p:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_fs_interval_contains
       (candle_fs_result_value_bound result)
       (candle_poly_denote_dim e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_poly_proxy_components) THEN
  ASM_REWRITE_TAC[candle_q_dim_jet_contains_components_def;
                  candle_q_dim_taylor_model_proxy_def;
                  candle_fs_result_to_q_def;
                  candle_q_dim_taylor_model_result_make_def;
                  candle_q_dim_taylor_model_result_value_bound_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_f_def;
                  candle_fs_interval_to_q_contains;
                  FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_result_poly_proxy_gradient_contains = prove
 (`!e boxes result (type_witness:real^N) (p:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_result_gradient_bounds result)
       (list_of_seq
         (\di. partial (di + 1) (candle_poly_denote_dim e) p)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_proxy_shape)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes result e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_poly_proxy_components)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes result e`)
     (CONJ
       (ASSUME
         `candle_fs_result_domain
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list)`)
       (ASSUME
         `(p:real^N) IN interval
           [candle_q_box_lower_vector boxes,
            candle_q_box_upper_vector boxes]`))) in
  let proxy_jet = rand (concl shape_th) in
  let gradient_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`; proxy_jet;
      `candle_poly_denote_dim e (p:real^N)`;
      `(\di. partial (di + 1) (candle_poly_denote_dim e)
        (p:real^N)):num->real`;
      `(\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e) (p:real^N)):num->num->real`]
     candle_q_dim_jet_components_gradient_contains)
   (CONJ shape_th components_th) in
  ACCEPT_TAC
   (REWRITE_RULE
     [candle_q_dim_taylor_model_proxy_def;
      candle_fs_result_to_q_def;
      candle_q_dim_taylor_model_result_make_def;
      candle_q_dim_taylor_model_result_gradient_bounds_def;
      candle_q_dim_jet_make_def;
      candle_q_dim_jet_gradient_def;
      candle_fs_interval_list_to_q_contains;
      FST; SND]
     gradient_th));;

let candle_fs_result_poly_box_hessian_contains = prove
 (`!e boxes result (type_witness:real^N) (p:real^N).
     candle_fs_result_poly_invariant type_witness boxes result e /\
     candle_fs_result_domain result /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_result_hessian result)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_poly_denote_dim e) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let shape_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_poly_proxy_shape)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (ASSUME
       `candle_fs_result_domain
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)`)) in
  let components_th = MATCH_MP
   (ISPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`;
      `p:real^N`]
     candle_fs_result_poly_proxy_components)
   (CONJ
     (ASSUME
       `candle_fs_result_poly_invariant
         (type_witness:real^N) boxes
         (result:
           bool#
           (((num#num)#(num#num))#((num#num)#(num#num))list)#
           ((num#num)#(num#num))#
           ((num#num)#(num#num))list#
           (((num#num)#(num#num))list)list)
         e`)
     (CONJ
       (ASSUME
         `candle_fs_result_domain
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list)`)
       (ASSUME
         `(p:real^N) IN interval
           [candle_q_box_lower_vector boxes,
            candle_q_box_upper_vector boxes]`))) in
  let proxy_jet = rand (concl shape_th) in
  let hessian_th = MATCH_MP
   (ISPECL
     [`dimindex (:N)`;
      proxy_jet;
      `candle_poly_denote_dim e (p:real^N)`;
      `(\di. partial (di + 1) (candle_poly_denote_dim e)
        (p:real^N)):num->real`;
      `(\di dj. partial2 (dj + 1) (di + 1)
        (candle_poly_denote_dim e) (p:real^N)):num->num->real`]
     candle_q_dim_jet_components_hessian_contains)
   (CONJ shape_th components_th) in
  let final_th =
   REWRITE_RULE
    [candle_q_dim_taylor_model_proxy_def;
     candle_fs_result_to_q_def;
     candle_q_dim_taylor_model_result_hessian_def;
     candle_q_dim_taylor_model_result_make_def;
     candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
     candle_fs_interval_matrix_to_q_contains; FST; SND]
    hessian_th in
  ACCEPT_TAC final_th);;

(* Fixed negation is exact at the chosen scale.  These conversion lemmas   *)
(* let the operation reuse the generic rational-jet shape proof while its  *)
(* enclosures remain fixed data.                                           *)

let candle_fs_interval_to_q_neg = prove
 (`!i. candle_fs_interval_to_q (candle_fs_interval_neg i) =
       candle_q_interval_neg (candle_fs_interval_to_q i)`,
  REWRITE_TAC[FORALL_PAIR_THM;
              candle_fs_interval_to_q_def;
              candle_fs_interval_neg_def;
              candle_fs_to_q_def; candle_fs_raw_neg_def;
              candle_q_interval_neg_def; candle_q_neg_def; FST; SND]);;

let candle_fs_interval_list_to_q_neg = prove
 (`!items.
     candle_fs_interval_list_to_q (candle_fs_interval_list_neg items) =
     candle_q_dim_interval_list_neg
       (candle_fs_interval_list_to_q items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_list_neg_def;
                  candle_fs_interval_list_to_q_def;
                  candle_q_dim_interval_list_neg_def;
                  candle_fs_interval_to_q_neg]);;

let candle_fs_interval_matrix_to_q_neg = prove
 (`!rows.
     candle_fs_interval_matrix_to_q (candle_fs_interval_matrix_neg rows) =
     candle_q_dim_interval_matrix_neg
       (candle_fs_interval_matrix_to_q rows)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_matrix_neg_def;
                  candle_fs_interval_matrix_to_q_def;
                  candle_q_dim_interval_matrix_neg_def;
                  candle_fs_interval_list_to_q_neg]);;

let candle_fs_first_to_q_neg = prove
 (`!first hessian.
     candle_fs_first_to_q
       (candle_fs_first_make
         (candle_fs_interval_neg (candle_fs_first_value first))
         (candle_fs_interval_list_neg
           (candle_fs_first_gradient first)))
       (candle_fs_interval_matrix_neg hessian) =
     candle_q_dim_jet_normalized_neg
       (candle_fs_first_to_q first hessian)`,
  REWRITE_TAC[candle_fs_first_to_q_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def; candle_fs_first_gradient_def;
              candle_q_dim_jet_f_def; candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_fs_interval_to_q_neg;
              candle_fs_interval_list_to_q_neg;
              candle_fs_interval_matrix_to_q_neg; FST; SND]);;

let candle_fs_interval_list_neg_contains = prove
 (`!intervals values.
     ALL2 candle_fs_interval_contains intervals values
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_neg intervals)
       (MAP (\x:real. --x) values)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; candle_fs_interval_list_neg_def] THEN
  ASM_MESON_TAC[candle_fs_interval_neg_sound]);;

let candle_fs_interval_matrix_neg_contains = prove
 (`!intervals values.
     ALL2 (ALL2 candle_fs_interval_contains) intervals values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_interval_matrix_neg intervals)
       (MAP (MAP (\x:real. --x)) values)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; candle_fs_interval_matrix_neg_def] THEN
  ASM_MESON_TAC[candle_fs_interval_list_neg_contains]);;

let candle_poly_denote_dim_neg_partial = prove
 (`!e (z:real^N) i.
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     partial i (candle_poly_denote_dim (Candle_poly_neg e)) z =
     --(partial i (candle_poly_denote_dim e) z)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_neg] THEN
  MATCH_MP_TAC partial_neg THEN
  MATCH_MP_TAC candle_dim_diff2c_imp_differentiable THEN
  MATCH_MP_TAC candle_poly_denote_dim_diff2c THEN
  ASM_REWRITE_TAC[]);;

let candle_poly_denote_dim_neg_partial2 = prove
 (`!e (z:real^N) i j.
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     partial2 j i (candle_poly_denote_dim (Candle_poly_neg e)) z =
     --(partial2 j i (candle_poly_denote_dim e) z)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_neg] THEN
  MATCH_MP_TAC second_partial_neg THEN
  MATCH_MP_TAC diff2c_imp_diff2 THEN
  MATCH_MP_TAC candle_poly_denote_dim_diff2c THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dim_jet_components_neg_sound = prove
 (`!e jet (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     candle_q_dim_jet_shape (dimindex (:N)) jet /\
     candle_q_dim_jet_contains_components (dimindex (:N)) jet
       (candle_poly_denote_dim e z)
       (\di. partial (di + 1) (candle_poly_denote_dim e) z)
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_poly_denote_dim e) z)
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_jet_normalized_neg jet)
       (candle_poly_denote_dim (Candle_poly_neg e) z)
       (\di. partial (di + 1)
         (candle_poly_denote_dim (Candle_poly_neg e)) z)
       (\di dj. partial2 (dj + 1) (di + 1)
         (candle_poly_denote_dim (Candle_poly_neg e)) z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_neg_def;
                candle_q_dim_jet_f_def; candle_q_dim_jet_make_def;
                candle_poly_denote_dim_neg; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN
    ASM_REWRITE_TAC[GSYM candle_q_dim_jet_f_def];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `candle_q_dim_jet_gradient_at
        (candle_q_dim_jet_normalized_neg jet) i =
      candle_q_interval_neg (candle_q_dim_jet_gradient_at jet i)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC
        (SPEC `dimindex (:N)`
          candle_q_dim_jet_normalized_neg_gradient_at) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[candle_poly_denote_dim_neg_partial] THEN
      MATCH_MP_TAC candle_q_interval_neg_sound THEN
      ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `candle_q_dim_jet_hessian_at
        (candle_q_dim_jet_normalized_neg jet) i j =
      candle_q_interval_neg (candle_q_dim_jet_hessian_at jet i j)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC
        (SPEC `dimindex (:N)`
          candle_q_dim_jet_normalized_neg_hessian_at) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[candle_poly_denote_dim_neg_partial2] THEN
      MATCH_MP_TAC candle_q_interval_neg_sound THEN
      ASM_MESON_TAC[]]]);;

let candle_map_neg_matrix_list_of_seq = prove
 (`!n (f:num->num->real).
     MAP (MAP (\x:real. --x))
       (list_of_seq (\i. list_of_seq (f i) n) n) =
     list_of_seq (\i. list_of_seq (\j. --(f i j)) n) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  REWRITE_TAC[LIST_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ];
    X_GEN_TAC `i:num` THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; o_THM] THEN
    REWRITE_TAC[LIST_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ];
      X_GEN_TAC `j:num` THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `EL j
          (MAP (\x:real. --x)
            (list_of_seq ((f:num->num->real) i) n)) =
       --(EL j (list_of_seq ((f:num->num->real) i) n))`
       SUBST1_TAC THENL
       [ASM_SIMP_TAC[EL_MAP; LENGTH_LIST_OF_SEQ];
        ASM_SIMP_TAC[EL_LIST_OF_SEQ]]]]);;

let candle_fs_result_neg_poly_invariant = prove
 (`!e boxes result (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fs_result_poly_invariant type_witness boxes result e
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_neg
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         result)
       (Candle_poly_neg e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_neg_def] THEN
  ASM_CASES_TAC
   `candle_fs_result_domain
     (result:
       bool#
       (((num#num)#(num#num))#((num#num)#(num#num))list)#
       ((num#num)#(num#num))#
       ((num#num)#(num#num))list#
       (((num#num)#(num#num))list)list)` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_result_complete_poly_invariant THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_valid_dim_def];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_fs_first_to_q_neg] THEN
      MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
      MATCH_MP_TAC
       (ISPECL
         [`e:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fs_result_poly_center_shape) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_fs_first_to_q_neg] THEN
      MATCH_MP_TAC candle_q_dim_jet_components_neg_sound THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC
         (ISPECL
           [`e:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_shape) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC
         (ISPECL
           [`e:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_components) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      let source_th = MATCH_MP
       (ISPECL
         [`e:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`;
          `p:real^N`]
         candle_fs_result_poly_box_hessian_contains)
       (CONJ
         (ASSUME
           `candle_fs_result_poly_invariant
             (type_witness:real^N) boxes
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)
             e`)
         (CONJ
           (ASSUME
             `candle_fs_result_domain
               (result:
                 bool#
                 (((num#num)#(num#num))#((num#num)#(num#num))list)#
                 ((num#num)#(num#num))#
                 ((num#num)#(num#num))list#
                 (((num#num)#(num#num))list)list)`)
           (ASSUME
             `(p:real^N) IN interval
               [candle_q_box_lower_vector boxes,
                candle_q_box_upper_vector boxes]`))) in
      let neg_th = MATCH_MP
       (ISPECL
         [`candle_fs_result_hessian
            (result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list)`;
          `list_of_seq
            (\di. list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim e) (p:real^N))
              (dimindex (:N)))
            (dimindex (:N))`]
         candle_fs_interval_matrix_neg_contains)
      source_th in
      MP_TAC neg_th THEN
      ASM_SIMP_TAC[candle_map_neg_matrix_list_of_seq;
                   candle_poly_denote_dim_neg_partial2]];
    REWRITE_TAC[candle_fs_result_poly_invariant_def;
                candle_fs_result_complete_domain] THEN
    ASM_REWRITE_TAC[]]);;

(* A constructor-facing form of the component invariant.  Operation closure *)
(* can prove fixed-data enclosures with ALL2 and recover the rational-jet    *)
(* interface here, without repeating lookup reasoning for every operation.   *)

let candle_fs_first_components_from_data = prove
 (`!n first hessian value gradient hessian_value.
     candle_q_dim_jet_shape n (candle_fs_first_to_q first hessian) /\
     candle_fs_interval_contains (candle_fs_first_value first) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient first)
       (list_of_seq gradient n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_value i) n) n)
     ==>
     candle_q_dim_jet_contains_components n
       (candle_fs_first_to_q first hessian)
       value gradient hessian_value`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_jet_contains_components_of_stacks THEN
  ASM_REWRITE_TAC[candle_fs_first_to_q_def;
                  candle_q_dim_jet_make_def;
                  candle_q_dim_jet_f_def;
                  candle_q_dim_jet_gradient_def;
                  candle_q_dim_jet_hessian_def;
                  candle_fs_interval_to_q_contains;
                  candle_fs_interval_list_to_q_contains;
                  candle_fs_interval_matrix_to_q_contains;
                  FST; SND]);;

(* Fixed addition preserves list shape and combines enclosures pointwise. *)

let candle_fs_interval_list_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_fs_interval_list_add xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                  candle_fs_interval_list_add_def]);;

let candle_fs_interval_matrix_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_fs_interval_matrix_add xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                  candle_fs_interval_matrix_add_def]);;

let candle_fs_interval_matrix_add_rows_width = prove
 (`!width xs ys.
     LENGTH xs = LENGTH ys /\
     ALL (\row. LENGTH row = width) xs /\
     ALL (\row. LENGTH row = width) ys
     ==>
     ALL (\row. LENGTH row = width)
       (candle_fs_interval_matrix_add xs ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ALL; NOT_SUC; SUC_INJ;
                  candle_fs_interval_matrix_add_def] THEN
  ASM_MESON_TAC[candle_fs_interval_list_add_length]);;

let candle_fs_interval_list_add_contains = prove
 (`!left_intervals left_values right_intervals right_values.
     LENGTH left_intervals = LENGTH right_intervals /\
     ALL2 candle_fs_interval_contains left_intervals left_values /\
     ALL2 candle_fs_interval_contains right_intervals right_values
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_add left_intervals right_intervals)
       (MAP2 (\x y:real. x + y) left_values right_values)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; SUC_INJ;
               ALL2; MAP2; MAP2_DEF;
               candle_fs_interval_list_add_def;
               candle_fs_interval_add_sound]);;

let candle_fs_interval_matrix_add_contains = prove
 (`!width left_intervals left_values right_intervals right_values.
     LENGTH left_intervals = LENGTH right_intervals /\
     ALL (\row. LENGTH row = width) left_intervals /\
     ALL (\row. LENGTH row = width) right_intervals /\
     ALL2 (ALL2 candle_fs_interval_contains)
       left_intervals left_values /\
     ALL2 (ALL2 candle_fs_interval_contains)
       right_intervals right_values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_interval_matrix_add left_intervals right_intervals)
       (MAP2 (MAP2 (\x y:real. x + y))
         left_values right_values)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; ALL; NOT_SUC; SUC_INJ;
               ALL2; MAP2; MAP2_DEF;
               candle_fs_interval_matrix_add_def;
               candle_fs_interval_list_add_contains]);;

let candle_map2_list_of_seq = prove
  (`!n (f:num->A) (g:num->B) (h:A->B->C).
     MAP2 h (list_of_seq f n) (list_of_seq g n) =
     list_of_seq (\i. h (f i) (g i)) n`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP2; MAP2_DEF; o_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CONS_11] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; o_THM]);;

let candle_map2_matrix_list_of_seq = prove
 (`!n (f:num->num->real) g.
     MAP2 (MAP2 (\x y:real. x + y))
       (list_of_seq (\i. list_of_seq (f i) n) n)
       (list_of_seq (\i. list_of_seq (g i) n) n) =
     list_of_seq
       (\i. list_of_seq (\j. f i j + g i j) n) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_map2_list_of_seq]);;

let candle_fs_first_add_shape = prove
 (`!n left_first left_hessian right_first right_hessian.
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q left_first left_hessian) /\
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q right_first right_hessian)
     ==>
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q
         (candle_fs_first_make
           (candle_fs_interval_add
             (candle_fs_first_value left_first)
             (candle_fs_first_value right_first))
           (candle_fs_interval_list_add
             (candle_fs_first_gradient left_first)
             (candle_fs_first_gradient right_first)))
         (candle_fs_interval_matrix_add
           left_hessian right_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_fs_first_to_q_shape]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_fs_first_gradient_def]) THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
     (ISPECL
       [`SND
          (left_first:
            ((num#num)#(num#num))#((num#num)#(num#num))list)`;
        `SND
          (right_first:
            ((num#num)#(num#num))#((num#num)#(num#num))list)`]
       candle_fs_interval_list_add_length) THEN
    ASM_REWRITE_TAC[];
    MP_TAC
     (ISPECL
       [`left_hessian:(((num#num)#(num#num))list)list`;
        `right_hessian:(((num#num)#(num#num))list)list`]
       candle_fs_interval_matrix_add_length) THEN
    ASM_REWRITE_TAC[];
    MP_TAC
     (ISPECL
       [`n:num`;
        `left_hessian:(((num#num)#(num#num))list)list`;
       `right_hessian:(((num#num)#(num#num))list)list`]
       candle_fs_interval_matrix_add_rows_width) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_first_add_components = prove
 (`!n left_first left_hessian right_first right_hessian
      left_value right_value left_gradient right_gradient
      left_hessian_value right_hessian_value.
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q left_first left_hessian) /\
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q right_first right_hessian) /\
     candle_fs_interval_contains
       (candle_fs_first_value left_first) left_value /\
     candle_fs_interval_contains
       (candle_fs_first_value right_first) right_value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient left_first)
       (list_of_seq left_gradient n) /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient right_first)
       (list_of_seq right_gradient n) /\
     ALL2 (ALL2 candle_fs_interval_contains) left_hessian
       (list_of_seq
         (\i. list_of_seq (left_hessian_value i) n) n) /\
     ALL2 (ALL2 candle_fs_interval_contains) right_hessian
       (list_of_seq
         (\i. list_of_seq (right_hessian_value i) n) n)
     ==>
     candle_q_dim_jet_contains_components n
       (candle_fs_first_to_q
         (candle_fs_first_make
           (candle_fs_interval_add
             (candle_fs_first_value left_first)
             (candle_fs_first_value right_first))
           (candle_fs_interval_list_add
             (candle_fs_first_gradient left_first)
             (candle_fs_first_gradient right_first)))
         (candle_fs_interval_matrix_add
           left_hessian right_hessian))
       (left_value + right_value)
       (\i. left_gradient i + right_gradient i)
       (\i j. left_hessian_value i j + right_hessian_value i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_fs_first_to_q_shape]) THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[candle_fs_first_value_def;
                 candle_fs_first_gradient_def]) THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_first_add_shape THEN
    ASM_REWRITE_TAC[candle_fs_first_to_q_shape;
                    candle_fs_first_gradient_def];
    REWRITE_TAC[candle_fs_first_make_def;
                candle_fs_first_value_def; FST; SND] THEN
    MATCH_MP_TAC candle_fs_interval_add_sound THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_make_def;
                candle_fs_first_gradient_def; FST; SND] THEN
    MP_TAC
     (ISPECL
       [`candle_fs_first_gradient
          (left_first:
            ((num#num)#(num#num))#((num#num)#(num#num))list)`;
        `list_of_seq (left_gradient:num->real) n`;
        `candle_fs_first_gradient
          (right_first:
            ((num#num)#(num#num))#((num#num)#(num#num))list)`;
       `list_of_seq (right_gradient:num->real) n`]
       candle_fs_interval_list_add_contains) THEN
    ASM_REWRITE_TAC[candle_fs_first_gradient_def;
                    candle_map2_list_of_seq];
    MP_TAC
     (ISPECL
       [`n:num`;
        `left_hessian:(((num#num)#(num#num))list)list`;
        `list_of_seq
          (\i. list_of_seq
            ((left_hessian_value:num->num->real) i) n) n`;
        `right_hessian:(((num#num)#(num#num))list)list`;
       `list_of_seq
          (\i. list_of_seq
            ((right_hessian_value:num->num->real) i) n) n`]
       candle_fs_interval_matrix_add_contains) THEN
    ASM_REWRITE_TAC[candle_map2_matrix_list_of_seq]]);;

let candle_poly_denote_dim_add_partial = prove
 (`!left right (z:real^N) i.
     candle_poly_valid_dim (dimindex (:N)) left /\
     candle_poly_valid_dim (dimindex (:N)) right
     ==>
     partial i
       (candle_poly_denote_dim (Candle_poly_add left right)) z =
     partial i (candle_poly_denote_dim left) z +
     partial i (candle_poly_denote_dim right) z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_add] THEN
  MP_TAC
   (SPECL
     [`(candle_poly_denote_dim left):real^N->real`; `i:num`;
      `(candle_poly_denote_dim right):real^N->real`; `z:real^N`]
     partial_add) THEN
  ASM_SIMP_TAC[candle_poly_denote_dim_diff2c;
               candle_dim_diff2c_imp_differentiable]);;

let candle_poly_denote_dim_add_partial2 = prove
 (`!left right (z:real^N) i j.
     candle_poly_valid_dim (dimindex (:N)) left /\
     candle_poly_valid_dim (dimindex (:N)) right
     ==>
     partial2 j i
       (candle_poly_denote_dim (Candle_poly_add left right)) z =
     partial2 j i (candle_poly_denote_dim left) z +
     partial2 j i (candle_poly_denote_dim right) z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_add] THEN
  MP_TAC
   (SPECL
     [`z:real^N`; `j:num`; `i:num`;
      `(candle_poly_denote_dim left):real^N->real`;
      `(candle_poly_denote_dim right):real^N->real`]
     second_partial_add) THEN
  ASM_SIMP_TAC[candle_poly_denote_dim_diff2c;
               diff2c_imp_diff2]);;

let candle_poly_denote_dim_add_hessian = prove
 (`!left right (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) left /\
     candle_poly_valid_dim (dimindex (:N)) right
     ==>
     list_of_seq
       (\i. list_of_seq
         (\j. partial2 (j + 1) (i + 1)
           (candle_poly_denote_dim (Candle_poly_add left right)) z)
         (dimindex (:N)))
       (dimindex (:N)) =
     list_of_seq
       (\i. list_of_seq
         (\j. partial2 (j + 1) (i + 1)
           (candle_poly_denote_dim left) z +
           partial2 (j + 1) (i + 1)
           (candle_poly_denote_dim right) z)
         (dimindex (:N)))
       (dimindex (:N))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_poly_denote_dim_add_partial2]);;

let candle_fs_result_add_poly_invariant = prove
 (`!left_expr right_expr boxes left_result right_result
      (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) left_expr /\
     candle_poly_valid_dim (dimindex (:N)) right_expr /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fs_result_poly_invariant
       type_witness boxes left_result left_expr /\
     candle_fs_result_poly_invariant
       type_witness boxes right_result right_expr
     ==>
     candle_fs_result_poly_invariant type_witness boxes
       (candle_fs_result_add
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         left_result right_result)
       (Candle_poly_add left_expr right_expr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_result_add_def] THEN
  ASM_CASES_TAC
   `candle_fs_result_domain
      (left_result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list) /\
    candle_fs_result_domain
      (right_result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_result_complete_poly_invariant THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_valid_dim_def];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_first_add_shape THEN CONJ_TAC THENL
       [MP_TAC
         (ISPECL
           [`left_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_shape) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`right_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_shape) THEN
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[candle_poly_denote_dim_add;
                   candle_poly_denote_dim_add_partial;
                   candle_poly_denote_dim_add_partial2] THEN
      MATCH_MP_TAC candle_fs_first_add_components THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC
         (ISPECL
           [`left_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_shape) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`right_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_shape) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`left_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_value_contains) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`right_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_value_contains) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`left_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_gradient_contains) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`right_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_gradient_contains) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`left_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_hessian_contains) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (ISPECL
           [`right_expr:candle_poly_expr`;
            `boxes:(((num#num)#num)#((num#num)#num))list`;
            `right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list`;
            `type_witness:real^N`]
           candle_fs_result_poly_center_hessian_contains) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      let domains_th = ASSUME
       `candle_fs_result_domain
          (left_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list) /\
        candle_fs_result_domain
          (right_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list)` in
      let left_domain_th = CONJUNCT1 domains_th in
      let right_domain_th = CONJUNCT2 domains_th in
      let left_th = MATCH_MP
       (ISPECL
         [`left_expr:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `left_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`;
          `p:real^N`]
         candle_fs_result_poly_box_hessian_contains)
       (CONJ
         (ASSUME
           `candle_fs_result_poly_invariant
             (type_witness:real^N) boxes left_result left_expr`)
         (CONJ
           left_domain_th
           (ASSUME
             `(p:real^N) IN interval
               [candle_q_box_lower_vector boxes,
                candle_q_box_upper_vector boxes]`))) in
      let right_th = MATCH_MP
       (ISPECL
         [`right_expr:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `right_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`;
          `p:real^N`]
         candle_fs_result_poly_box_hessian_contains)
       (CONJ
         (ASSUME
           `candle_fs_result_poly_invariant
             (type_witness:real^N) boxes right_result right_expr`)
         (CONJ
           right_domain_th
           (ASSUME
             `(p:real^N) IN interval
               [candle_q_box_lower_vector boxes,
                candle_q_box_upper_vector boxes]`))) in
      let left_shape_th = MATCH_MP
       (ISPECL
         [`left_expr:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `left_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fs_result_poly_center_shape)
       (CONJ
         (ASSUME
           `candle_fs_result_poly_invariant
             (type_witness:real^N) boxes left_result left_expr`)
         left_domain_th) in
      let right_shape_th = MATCH_MP
       (ISPECL
         [`right_expr:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `right_result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fs_result_poly_center_shape)
       (CONJ
         (ASSUME
           `candle_fs_result_poly_invariant
             (type_witness:real^N) boxes right_result right_expr`)
         right_domain_th) in
      STRIP_ASSUME_TAC
       (REWRITE_RULE[candle_fs_first_to_q_shape] left_shape_th) THEN
      STRIP_ASSUME_TAC
       (REWRITE_RULE[candle_fs_first_to_q_shape] right_shape_th) THEN
      let hessian_contains_pred =
       `\values:(real list)list.
          ALL2 (ALL2 candle_fs_interval_contains)
            (candle_fs_interval_matrix_add
              (candle_fs_result_hessian
                (left_result:
                  bool#
                  (((num#num)#(num#num))#
                    ((num#num)#(num#num))list)#
                  ((num#num)#(num#num))#
                  ((num#num)#(num#num))list#
                  (((num#num)#(num#num))list)list))
              (candle_fs_result_hessian
                (right_result:
                  bool#
                  (((num#num)#(num#num))#
                    ((num#num)#(num#num))list)#
                  ((num#num)#(num#num))#
                  ((num#num)#(num#num))list#
                  (((num#num)#(num#num))list)list)))
            values` in
      let add_hessian_th = MATCH_MP
       (ISPECL
         [`left_expr:candle_poly_expr`;
          `right_expr:candle_poly_expr`;
          `p:real^N`]
         candle_poly_denote_dim_add_hessian)
       (CONJ
         (ASSUME
           `candle_poly_valid_dim (dimindex (:N)) left_expr`)
         (ASSUME
           `candle_poly_valid_dim (dimindex (:N)) right_expr`)) in
      let add_hessian_contains_th =
       CONV_RULE (BINOP_CONV BETA_CONV)
        (AP_TERM hessian_contains_pred add_hessian_th) in
      let map2_hessian_th = BETA_RULE (ISPECL
       [`dimindex (:N)`;
        `(\di dj. partial2 (dj + 1) (di + 1)
           (candle_poly_denote_dim left_expr) (p:real^N))`;
        `(\di dj. partial2 (dj + 1) (di + 1)
           (candle_poly_denote_dim right_expr) (p:real^N))`]
       candle_map2_matrix_list_of_seq) in
      let map2_hessian_contains_th =
       CONV_RULE (BINOP_CONV BETA_CONV)
        (AP_TERM hessian_contains_pred map2_hessian_th) in
      let matrix_th = MATCH_MP
       (ISPECL
         [`dimindex (:N)`;
          `candle_fs_result_hessian
            (left_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list)`;
          `list_of_seq
            (\di. list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim left_expr) (p:real^N))
              (dimindex (:N)))
            (dimindex (:N))`;
          `candle_fs_result_hessian
            (right_result:
              bool#
              (((num#num)#(num#num))#((num#num)#(num#num))list)#
              ((num#num)#(num#num))#
              ((num#num)#(num#num))list#
              (((num#num)#(num#num))list)list)`;
          `list_of_seq
            (\di. list_of_seq
              (\dj. partial2 (dj + 1) (di + 1)
                (candle_poly_denote_dim right_expr) (p:real^N))
              (dimindex (:N)))
            (dimindex (:N))`]
         candle_fs_interval_matrix_add_contains)
       (CONJ
         (TRANS
           (ASSUME
             `LENGTH
                (candle_fs_result_hessian
                  (left_result:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list)) =
              dimindex (:N)`)
           (SYM
             (ASSUME
               `LENGTH
                  (candle_fs_result_hessian
                    (right_result:
                      bool#
                      (((num#num)#(num#num))#
                        ((num#num)#(num#num))list)#
                      ((num#num)#(num#num))#
                      ((num#num)#(num#num))list#
                      (((num#num)#(num#num))list)list)) =
                dimindex (:N)`)))
         (CONJ
           (ASSUME
             `ALL (\row. LENGTH row = dimindex (:N))
                (candle_fs_result_hessian
                  (left_result:
                    bool#
                    (((num#num)#(num#num))#
                      ((num#num)#(num#num))list)#
                    ((num#num)#(num#num))#
                    ((num#num)#(num#num))list#
                    (((num#num)#(num#num))list)list))`)
           (CONJ
             (ASSUME
               `ALL (\row. LENGTH row = dimindex (:N))
                  (candle_fs_result_hessian
                    (right_result:
                      bool#
                      (((num#num)#(num#num))#
                        ((num#num)#(num#num))list)#
                      ((num#num)#(num#num))#
                      ((num#num)#(num#num))list#
                      (((num#num)#(num#num))list)list))`)
             (CONJ left_th right_th)))) in
      let sum_matrix_th =
       EQ_MP map2_hessian_contains_th matrix_th in
      let result_th =
       EQ_MP (SYM add_hessian_contains_th) sum_matrix_th in
      ACCEPT_TAC
       result_th];
    REWRITE_TAC[candle_fs_result_poly_invariant_def;
                candle_fs_result_complete_domain] THEN
    ASM_REWRITE_TAC[]]);;

(* Multiplication accumulates products at denominator scale squared and only *)
(* rounds once at the completed-result boundary.  Keep the corresponding     *)
(* list and matrix facts outside the evaluator so the hot path remains data. *)

let candle_fs_raw_interval_add_sound = prove
 (`!left right x y.
     candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale) left x /\
     candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale) right y
     ==> candle_fs_raw_interval_contains
           (candle_fs_scale * candle_fs_scale)
           (candle_fs_raw_interval_add left right) (x + y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_interval_contains_def;
              candle_fs_raw_interval_add_def;
              candle_fs_raw_product_add_real; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_raw_interval_list_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_fs_raw_interval_list_add xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                  candle_fs_raw_interval_list_add_def]);;

let candle_fs_raw_interval_list_scale_length = prove
 (`!scalar items.
     LENGTH (candle_fs_raw_interval_list_scale scalar items) = LENGTH items`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; candle_fs_raw_interval_list_scale_def]);;

let candle_fs_raw_interval_matrix_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_fs_raw_interval_matrix_add xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                  candle_fs_raw_interval_matrix_add_def]);;

let candle_fs_raw_interval_matrix_add_rows_width = prove
 (`!width xs ys.
     LENGTH xs = LENGTH ys /\
     ALL (\row. LENGTH row = width) xs /\
     ALL (\row. LENGTH row = width) ys
     ==> ALL (\row. LENGTH row = width)
           (candle_fs_raw_interval_matrix_add xs ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ALL; NOT_SUC; SUC_INJ;
                  candle_fs_raw_interval_matrix_add_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_list_add_length]);;

let candle_fs_raw_interval_matrix_scale_length = prove
 (`!scalar rows.
     LENGTH (candle_fs_raw_interval_matrix_scale scalar rows) = LENGTH rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; candle_fs_raw_interval_matrix_scale_def]);;

let candle_fs_raw_interval_matrix_scale_rows_width = prove
 (`!scalar rows width.
     ALL (\row. LENGTH row = width) rows
     ==> ALL (\row. LENGTH row = width)
           (candle_fs_raw_interval_matrix_scale scalar rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ALL; candle_fs_raw_interval_matrix_scale_def];
    GEN_TAC THEN
    REWRITE_TAC[ALL; candle_fs_raw_interval_matrix_scale_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_fs_raw_interval_list_scale_length];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fs_raw_interval_matrix_scale_shape = prove
 (`!scalar rows width.
     ALL (\row. LENGTH row = width) rows
     ==>
     LENGTH (candle_fs_raw_interval_matrix_scale scalar rows) = LENGTH rows /\
     ALL (\row. LENGTH row = width)
       (candle_fs_raw_interval_matrix_scale scalar rows)`,
  MESON_TAC[candle_fs_raw_interval_matrix_scale_length;
            candle_fs_raw_interval_matrix_scale_rows_width]);;

let candle_fs_raw_interval_outer_shape = prove
 (`!xs ys.
     LENGTH (candle_fs_raw_interval_outer xs ys) = LENGTH xs /\
     ALL (\row. LENGTH row = LENGTH ys)
       (candle_fs_raw_interval_outer xs ys)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ALL; candle_fs_raw_interval_outer_def;
                  candle_fs_raw_interval_list_scale_length]);;

let candle_fs_raw_interval_list_round_length = prove
 (`!denominator items.
     LENGTH (candle_fs_raw_interval_list_round denominator items) =
     LENGTH items`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; candle_fs_raw_interval_list_round_def]);;

let candle_fs_raw_interval_matrix_round_length = prove
 (`!denominator rows.
     LENGTH (candle_fs_raw_interval_matrix_round denominator rows) =
     LENGTH rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; candle_fs_raw_interval_matrix_round_def]);;

let candle_fs_raw_interval_matrix_round_rows_width = prove
 (`!denominator rows width.
     ALL (\row. LENGTH row = width) rows
     ==> ALL (\row. LENGTH row = width)
           (candle_fs_raw_interval_matrix_round denominator rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ALL; candle_fs_raw_interval_matrix_round_def];
    GEN_TAC THEN
    REWRITE_TAC[ALL; candle_fs_raw_interval_matrix_round_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_fs_raw_interval_list_round_length];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fs_raw_interval_matrix_round_shape = prove
 (`!denominator rows width.
     ALL (\row. LENGTH row = width) rows
     ==>
     LENGTH (candle_fs_raw_interval_matrix_round denominator rows) =
       LENGTH rows /\
     ALL (\row. LENGTH row = width)
       (candle_fs_raw_interval_matrix_round denominator rows)`,
  MESON_TAC[candle_fs_raw_interval_matrix_round_length;
            candle_fs_raw_interval_matrix_round_rows_width]);;

let candle_fs_raw_interval_list_add_contains = prove
 (`!left_intervals left_values right_intervals right_values.
     LENGTH left_intervals = LENGTH right_intervals /\
     ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale))
       left_intervals left_values /\
     ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale))
       right_intervals right_values
     ==>
     ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale))
       (candle_fs_raw_interval_list_add left_intervals right_intervals)
       (MAP2 (\x y:real. x + y) left_values right_values)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; SUC_INJ; ALL2; MAP2; MAP2_DEF;
               candle_fs_raw_interval_list_add_def;
               candle_fs_raw_interval_add_sound]);;

let candle_fs_raw_interval_list_scale_contains = prove
 (`!scalar scalar_value intervals values.
     candle_fs_interval_contains scalar scalar_value /\
     ALL2 candle_fs_interval_contains intervals values
     ==>
     ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale))
       (candle_fs_raw_interval_list_scale scalar intervals)
       (MAP (\x:real. scalar_value * x) values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`ALL2 candle_fs_interval_contains intervals values`;
    `candle_fs_interval_contains scalar scalar_value`] THEN
  SPEC_TAC (`values:real list`,`values:real list`) THEN
  SPEC_TAC
   (`intervals:((num#num)#(num#num))list`,
    `intervals:((num#num)#(num#num))list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; candle_fs_raw_interval_list_scale_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_mul_sound]);;

let candle_fs_raw_interval_matrix_add_contains = prove
 (`!width left_intervals left_values right_intervals right_values.
     LENGTH left_intervals = LENGTH right_intervals /\
     ALL (\row. LENGTH row = width) left_intervals /\
     ALL (\row. LENGTH row = width) right_intervals /\
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)))
       left_intervals left_values /\
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)))
       right_intervals right_values
     ==>
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)))
       (candle_fs_raw_interval_matrix_add left_intervals right_intervals)
       (MAP2 (MAP2 (\x y:real. x + y)) left_values right_values)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; ALL; NOT_SUC; SUC_INJ; ALL2; MAP2; MAP2_DEF;
               candle_fs_raw_interval_matrix_add_def;
               candle_fs_raw_interval_list_add_contains]);;

let candle_fs_raw_interval_matrix_scale_contains = prove
 (`!scalar scalar_value intervals values.
     candle_fs_interval_contains scalar scalar_value /\
     ALL2 (ALL2 candle_fs_interval_contains) intervals values
     ==>
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)))
       (candle_fs_raw_interval_matrix_scale scalar intervals)
       (MAP (MAP (\x:real. scalar_value * x)) values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`ALL2 (ALL2 candle_fs_interval_contains) intervals values`;
    `candle_fs_interval_contains scalar scalar_value`] THEN
  SPEC_TAC (`values:(real list)list`,`values:(real list)list`) THEN
  SPEC_TAC
   (`intervals:(((num#num)#(num#num))list)list`,
    `intervals:(((num#num)#(num#num))list)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; candle_fs_raw_interval_matrix_scale_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_list_scale_contains]);;

let candle_fs_raw_interval_outer_contains = prove
 (`!left_intervals left_values right_intervals right_values.
     ALL2 candle_fs_interval_contains left_intervals left_values /\
     ALL2 candle_fs_interval_contains right_intervals right_values
     ==>
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)))
       (candle_fs_raw_interval_outer left_intervals right_intervals)
       (MAP (\x:real. MAP (\y:real. x * y) right_values) left_values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`ALL2 candle_fs_interval_contains left_intervals left_values`;
    `ALL2 candle_fs_interval_contains right_intervals right_values`] THEN
  SPEC_TAC (`left_values:real list`,`left_values:real list`) THEN
  SPEC_TAC
   (`left_intervals:((num#num)#(num#num))list`,
    `left_intervals:((num#num)#(num#num))list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; candle_fs_raw_interval_outer_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_list_scale_contains]);;

let candle_fs_raw_interval_list_round_contains = prove
 (`!intervals values.
     ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale)) intervals values
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_raw_interval_list_round candle_fs_scale intervals)
       values`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; candle_fs_raw_interval_list_round_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_round_sound;
                candle_fs_scale_pos]);;

let candle_fs_raw_interval_matrix_round_contains = prove
 (`!intervals values.
     ALL2 (ALL2 (candle_fs_raw_interval_contains
       (candle_fs_scale * candle_fs_scale))) intervals values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_raw_interval_matrix_round candle_fs_scale intervals)
       values`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; candle_fs_raw_interval_matrix_round_def] THEN
  ASM_MESON_TAC[candle_fs_raw_interval_list_round_contains]);;

let candle_fs_raw_mul_gradient_length = prove
 (`!n right_value left_gradient left_value right_gradient.
     LENGTH left_gradient = n /\ LENGTH right_gradient = n
     ==>
     LENGTH
       (candle_fs_raw_interval_list_round candle_fs_scale
         (candle_fs_raw_interval_list_add
           (candle_fs_raw_interval_list_scale right_value left_gradient)
           (candle_fs_raw_interval_list_scale left_value right_gradient))) = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_raw_interval_list_round_length;
               candle_fs_raw_interval_list_add_length;
               candle_fs_raw_interval_list_scale_length]);;

let candle_all2_length = prove
 (`!P (xs:A list) (ys:B list).
     ALL2 P xs ys ==> LENGTH xs = LENGTH ys`,
  STRIP_TAC THEN
  REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; LENGTH] THEN
  ASM_MESON_TAC[]);;

let candle_fs_raw_mul_center_value_gradient_contains = prove
 (`!n left_value_interval right_value_interval
      left_gradient_intervals right_gradient_intervals
      left_value right_value left_gradient right_gradient.
     candle_fs_interval_contains left_value_interval left_value /\
     candle_fs_interval_contains right_value_interval right_value /\
     ALL2 candle_fs_interval_contains left_gradient_intervals
       (list_of_seq left_gradient n) /\
     ALL2 candle_fs_interval_contains right_gradient_intervals
       (list_of_seq right_gradient n)
     ==>
     candle_fs_interval_contains
       (candle_fs_raw_interval_round candle_fs_scale
         (candle_fs_raw_interval_mul
           left_value_interval right_value_interval))
       (left_value * right_value) /\
     ALL2 candle_fs_interval_contains
       (candle_fs_raw_interval_list_round candle_fs_scale
         (candle_fs_raw_interval_list_add
           (candle_fs_raw_interval_list_scale
             right_value_interval left_gradient_intervals)
           (candle_fs_raw_interval_list_scale
             left_value_interval right_gradient_intervals)))
       (list_of_seq
         (\i. right_value * left_gradient i +
              left_value * right_gradient i) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_length_th = MATCH_MP
   (ISPECL
     [`candle_fs_interval_contains`;
      `left_gradient_intervals:((num#num)#(num#num))list`;
      `list_of_seq (left_gradient:num->real) n`]
     candle_all2_length)
   (ASSUME
     `ALL2 candle_fs_interval_contains left_gradient_intervals
       (list_of_seq left_gradient n)`) in
  let right_length_th = MATCH_MP
   (ISPECL
     [`candle_fs_interval_contains`;
      `right_gradient_intervals:((num#num)#(num#num))list`;
      `list_of_seq (right_gradient:num->real) n`]
     candle_all2_length)
   (ASSUME
     `ALL2 candle_fs_interval_contains right_gradient_intervals
       (list_of_seq right_gradient n)`) in
  ASSUME_TAC (REWRITE_RULE[LENGTH_LIST_OF_SEQ] left_length_th) THEN
  ASSUME_TAC (REWRITE_RULE[LENGTH_LIST_OF_SEQ] right_length_th) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_mul_sound THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_raw_interval_list_round_contains THEN
    MP_TAC
     (ISPECL
       [`candle_fs_raw_interval_list_scale
          right_value_interval left_gradient_intervals`;
        `MAP (\x:real. right_value * x)
          (list_of_seq left_gradient n)`;
        `candle_fs_raw_interval_list_scale
          left_value_interval right_gradient_intervals`;
        `MAP (\x:real. left_value * x)
          (list_of_seq right_gradient n)`]
       candle_fs_raw_interval_list_add_contains) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[candle_fs_raw_interval_list_scale_length];
        MATCH_MP_TAC candle_fs_raw_interval_list_scale_contains THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_fs_raw_interval_list_scale_contains THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[MAP_LIST_OF_SEQ; o_THM;
                  candle_map2_list_of_seq]]]);;

end;;
