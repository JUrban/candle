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
open Candle_cv_polynomial_expr_diff;;
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

end;;
