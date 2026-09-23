(* ========================================================================== *)
(* Dimension-generic box bridge for the reflected Flyspeck checker.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file turns an exact-rational box list    *)
(* into Flyspeck's finite Cartesian domain, center, and radius vectors.       *)
(* The later checker theorem can therefore instantiate [m_taylor_upper_bound] *)
(* without a per-expression analytic construction.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml";;
needs "candle/cv_compute_whole_box_dim_taylor_sound.ml";;
needs "candle/cv_compute_polynomial_expr_dim_check.ml";;

let _ = ();;

module Candle_cv_polynomial_expr_flyspeck_dim_sound = struct

open Multivariate_taylor;;
open Ssreflect;;
open Ssrnat;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;

let candle_q_box_lower_vector_def = new_definition
 `candle_q_box_lower_vector
    (boxes:(((num#num)#num)#((num#num)#num))list) : real^N =
    lambda i. candle_q_real (FST (EL (i - 1) boxes))`;;

let candle_q_box_upper_vector_def = new_definition
 `candle_q_box_upper_vector
    (boxes:(((num#num)#num)#((num#num)#num))list) : real^N =
    lambda i. candle_q_real (SND (EL (i - 1) boxes))`;;

let candle_q_box_center_vector_def = new_definition
 `candle_q_box_center_vector
    (boxes:(((num#num)#num)#((num#num)#num))list) : real^N =
    lambda i. candle_q_real (candle_q_midpoint (EL (i - 1) boxes))`;;

let candle_q_box_radius_vector_def = new_definition
 `candle_q_box_radius_vector
    (boxes:(((num#num)#num)#((num#num)#num))list) : real^N =
    lambda i. candle_q_real (candle_q_radius (EL (i - 1) boxes))`;;

let candle_q_box_lower_vector_component = prove
 (`!boxes i.
     i IN 1..dimindex (:N)
     ==>
     (candle_q_box_lower_vector boxes : real^N)$i =
       candle_q_real (FST (EL (i - 1) boxes))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_box_lower_vector_def] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN
  ASM_MESON_TAC[IN_NUMSEG]);;

let candle_q_box_upper_vector_component = prove
 (`!boxes i.
     i IN 1..dimindex (:N)
     ==>
     (candle_q_box_upper_vector boxes : real^N)$i =
       candle_q_real (SND (EL (i - 1) boxes))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_box_upper_vector_def] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN
  ASM_MESON_TAC[IN_NUMSEG]);;

let candle_q_box_center_vector_component = prove
 (`!boxes i.
     i IN 1..dimindex (:N)
     ==>
     (candle_q_box_center_vector boxes : real^N)$i =
       candle_q_real (candle_q_midpoint (EL (i - 1) boxes))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_box_center_vector_def] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN
  ASM_MESON_TAC[IN_NUMSEG]);;

let candle_q_box_radius_vector_component = prove
 (`!boxes i.
     i IN 1..dimindex (:N)
     ==>
     (candle_q_box_radius_vector boxes : real^N)$i =
       candle_q_real (candle_q_radius (EL (i - 1) boxes))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_box_radius_vector_def] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN
  ASM_MESON_TAC[IN_NUMSEG]);;

let candle_q_box_center_vector_list = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     list_of_seq
       (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
       (dimindex (:N)) =
     MAP (\box. candle_q_real (candle_q_midpoint box)) boxes`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC LE_ADDR;
      REWRITE_TAC[GSYM ADD1; LE_SUC_LT] THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP;
                 candle_q_box_center_vector_component; ADD_SUB]]);;

let candle_q_box_radius_vector_list = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     list_of_seq
       (\k. (candle_q_box_radius_vector boxes : real^N)$(k + 1))
       (dimindex (:N)) =
     MAP (\box. candle_q_real (candle_q_radius box)) boxes`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC LE_ADDR;
      REWRITE_TAC[GSYM ADD1; LE_SUC_LT] THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP;
                 candle_q_box_radius_vector_component; ADD_SUB]]);;

let candle_q_radius_list_map = prove
 (`!boxes.
     candle_q_radius_list boxes = MAP candle_q_radius boxes`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_radius_list_def; MAP]);;

let candle_q_radius_list_vector_component = prove
 (`!boxes i.
     LENGTH boxes = dimindex (:N) /\
     i IN 1..dimindex (:N)
     ==>
     candle_q_real (EL (i - 1) (candle_q_radius_list boxes)) =
     (candle_q_box_radius_vector boxes : real^N)$i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `i - 1 <
    LENGTH (boxes:(((num#num)#num)#((num#num)#num))list)`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL
     [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
      REWRITE_TAC[IN_NUMSEG] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `i <= dimindex (:N)` ASSUME_TAC THENL
     [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
      REWRITE_TAC[IN_NUMSEG] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUB_ADD];
      REWRITE_TAC[GSYM LE_SUC_LT; ADD1] THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[candle_q_radius_list_map; EL_MAP;
                 candle_q_box_radius_vector_component]]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE vector_encodings";;

let candle_q_center_environment_vector_contains = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_stack_contains
       (candle_q_center_environment_list boxes)
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `boxes:(((num#num)#num)#((num#num)#num))list`
    candle_q_center_environment_list_contains) THEN
  ASM_SIMP_TAC[candle_q_box_center_vector_list]);;

let candle_q_box_m_cell_domain = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     m_cell_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_center_vector boxes)
       (candle_q_box_radius_vector boxes)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[m_cell_domain] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_box_lower_vector_component;
               candle_q_box_upper_vector_component;
               candle_q_box_center_vector_component;
               candle_q_box_radius_vector_component] THEN
  MP_TAC
   (SPEC
     `EL (i - 1)
       (boxes:(((num#num)#num)#((num#num)#num))list)`
     candle_q_box_midpoint_radius) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC candle_q_box_valid_list_el THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    MESON_TAC[]]);;

let candle_q_box_stack_contains_vector = prove
 (`!boxes (z:real^N).
     LENGTH boxes = dimindex (:N) /\
     z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_stack_contains boxes
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (LABEL_TAC "box_length") (LABEL_TAC "z_in")) THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  SUBGOAL_THEN
   `(boxes:(((num#num)#num)#((num#num)#num))list) =
    list_of_seq (\k. EL k boxes) (dimindex (:N))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_LIST_OF_SEQ] THEN
    USE_THEN "box_length" ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC LE_ADDR;
      REWRITE_TAC[GSYM ADD1; LE_SUC_LT] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "z_in" (MP_TAC o REWRITE_RULE[IN_INTERVAL]) THEN
  DISCH_THEN (MP_TAC o SPEC `k + 1`) THEN
  DISCH_THEN
   (fun th -> MP_TAC
     (MATCH_MP th
       (REWRITE_RULE[IN_NUMSEG]
         (ASSUME `k + 1 IN 1..dimindex (:N)`)))) THEN
  ASM_SIMP_TAC[candle_q_interval_contains_def;
               candle_q_box_lower_vector_component;
               candle_q_box_upper_vector_component; ADD_SUB]);;

let candle_poly_center_interval_contains = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_interval_contains
       (candle_q_program_interval
         (candle_q_center_environment_list boxes)
         (candle_poly_compile e))
       (candle_poly_denote_dim e
         (candle_q_box_center_vector boxes : real^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`e:candle_poly_expr`;
      `candle_q_center_environment_list boxes`;
      `list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))`]
     candle_poly_interval_sound) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC candle_q_center_environment_vector_contains THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[candle_poly_value_list_fun;
                 candle_poly_denote_dim_def]]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE box_bridge";;

(* The reflected accumulators are list folds, whereas Flyspeck's Taylor     *)
(* contract is stated with finite sums.  This conversion is independent of  *)
(* the expression language and is reused for the gradient and Hessian rows. *)

let candle_itlist2_eq_sum = prove
 (`!(f:A->B->real) l1 l2.
     LENGTH l1 <= LENGTH l2
     ==>
     ITLIST2 (\x y z. f x y + z) l1 l2 (&0) =
     sum (1..LENGTH l1)
       (\i. f (EL (i - 1) l1) (EL (i - 1) l2))`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ITLIST2_DEF] THEN TRY ARITH_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH];
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[LE_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t':B list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> REWRITE_TAC[TL; th]) THEN
  REWRITE_TAC[GSYM add1n] THEN
  new_rewrite [] [] SUM_ADD_SPLIT THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[TWO; add1n; SUM_SING_NUMSEG; subnn; EL; HD] THEN
  REWRITE_TAC[GSYM addn1; SUM_OFFSET; REAL_EQ_ADD_LCANCEL] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> (i + 1) - 1 = SUC (i - 1)`;
               EL; TL]);;

let candle_q_dot_list_of_seq_sum = prove
 (`!boxes (g:num->real).
     LENGTH boxes = dimindex (:N)
     ==>
     ITLIST2
       (\r y total. candle_q_real r * abs y + total)
       (candle_q_radius_list boxes)
       (list_of_seq g (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs (g (i - 1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`\r y. candle_q_real r * abs y`;
      `candle_q_radius_list boxes`;
      `list_of_seq (g:num->real) (dimindex (:N))`]
     candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length;
                    LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[candle_q_radius_list_length] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ASM_SIMP_TAC[candle_q_radius_list_vector_component;
                 EL_LIST_OF_SEQ]]);;

let candle_q_weighted_rows_list_of_seq_sum = prove
 (`!boxes (h:num->num->real).
     LENGTH boxes = dimindex (:N)
     ==>
     ITLIST2
       (\w values total.
          candle_q_real w *
          ITLIST2
            (\r y subtotal. candle_q_real r * abs y + subtotal)
            (candle_q_radius_list boxes) values (&0) + total)
       (candle_q_radius_list boxes)
       (list_of_seq
         (\di. list_of_seq (h di) (dimindex (:N)))
         (dimindex (:N))) (&0) =
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                   abs (h (i - 1) (j - 1))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (ISPECL
     [`\w values.
        candle_q_real w *
        ITLIST2
          (\r y subtotal. candle_q_real r * abs y + subtotal)
          (candle_q_radius_list boxes) values (&0)`;
      `candle_q_radius_list boxes`;
      `list_of_seq
        (\di. list_of_seq ((h:num->num->real) di) (dimindex (:N)))
        (dimindex (:N))`]
     candle_itlist2_eq_sum) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[candle_q_radius_list_length;
                    LENGTH_LIST_OF_SEQ; LE_REFL];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[BETA_RULE th])] THEN
  ASM_REWRITE_TAC[candle_q_radius_list_length] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i - 1 < dimindex (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `i IN 1..dimindex (:N)` THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ASM_SIMP_TAC[candle_q_radius_list_vector_component;
                 EL_LIST_OF_SEQ; candle_q_dot_list_of_seq_sum]]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE sum_correspondence";;

let candle_poly_gradient_taylor_sum_bound = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            abs
              (partial i (candle_poly_denote_dim e)
                (candle_q_box_center_vector boxes : real^N))) <=
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_program_interval_list
           (candle_q_center_environment_list boxes)
           (candle_poly_gradient_programs (dimindex (:N)) e)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_q_interval_contains
      (candle_q_program_interval_list
        (candle_q_center_environment_list boxes)
        (candle_poly_gradient_programs (dimindex (:N)) e))
      (list_of_seq
        (\di. partial (di + 1) (candle_poly_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N)))`
   (LABEL_TAC "gradient_contains") THENL
   [MP_TAC
     (SPECL
       [`dimindex (:N)`; `e:candle_poly_expr`;
        `candle_q_center_environment_list boxes`;
        `list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))`]
       candle_poly_gradient_programs_interval_sound) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC candle_q_center_environment_vector_contains THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[candle_poly_gradient_flyspeck_partials]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial i (candle_poly_denote_dim e)
               (candle_q_box_center_vector boxes : real^N))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           abs
             (partial ((i - 1) + 1) (candle_poly_denote_dim e)
               (candle_q_box_center_vector boxes : real^N)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  MP_TAC
   (SPECL
     [`candle_q_radius_list boxes`;
      `list_of_seq
        (\di. partial (di + 1) (candle_poly_denote_dim e)
          (candle_q_box_center_vector boxes : real^N))
        (dimindex (:N))`;
      `candle_q_program_interval_list
        (candle_q_center_environment_list boxes)
        (candle_poly_gradient_programs (dimindex (:N)) e)`]
     candle_q_dot_abs_upper_sound) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      USE_THEN "gradient_contains" ACCEPT_TAC;
      ASM_REWRITE_TAC[candle_q_radius_list_length;
                      LENGTH_LIST_OF_SEQ]];
    ASM_SIMP_TAC[candle_q_dot_list_of_seq_sum]]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE gradient_bound";;

let candle_poly_hessian_taylor_sum_bound = prove
 (`!e boxes (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     sum (1..dimindex (:N))
       (\i. (candle_q_box_radius_vector boxes : real^N)$i *
            sum (1..dimindex (:N))
              (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                   abs
                     (partial2 j i (candle_poly_denote_dim e)
                       (z:real^N)))) <=
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_program_interval_matrix boxes
           (candle_poly_hessian_programs (dimindex (:N)) e)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_poly_hessian (dimindex (:N))
      (list_of_seq (\k. (z:real^N)$(k + 1)) (dimindex (:N))) e =
    list_of_seq
      (\di.
         list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_poly_denote_dim e) (z:real^N))
           (dimindex (:N)))
      (dimindex (:N))`
   (LABEL_TAC "hessian_values") THENL
   [MATCH_MP_TAC candle_poly_hessian_flyspeck_partials THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_q_stack_contains
      (candle_q_program_interval_matrix boxes
        (candle_poly_hessian_programs (dimindex (:N)) e))
      (list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N)))`
   (LABEL_TAC "hessian_contains") THENL
   [USE_THEN "hessian_values"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC candle_poly_hessian_programs_interval_sound THEN
    MATCH_MP_TAC candle_q_box_stack_contains_vector THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs (partial2 j i (candle_poly_denote_dim e)
                    (z:real^N)))) =
    sum (1..dimindex (:N))
      (\i. (candle_q_box_radius_vector boxes : real^N)$i *
           sum (1..dimindex (:N))
             (\j. (candle_q_box_radius_vector boxes : real^N)$j *
                  abs
                    (partial2 ((j - 1) + 1) ((i - 1) + 1)
                      (candle_poly_denote_dim e) (z:real^N))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  MP_TAC
   (SPECL
     [`candle_q_radius_list boxes`;
      `candle_q_radius_list boxes`;
      `list_of_seq
        (\di.
           list_of_seq
             (\dj. partial2 (dj + 1) (di + 1)
               (candle_poly_denote_dim e) (z:real^N))
             (dimindex (:N)))
        (dimindex (:N))`;
      `candle_q_program_interval_matrix boxes
        (candle_poly_hessian_programs (dimindex (:N)) e)`]
     candle_q_weighted_rows_abs_upper_sound) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_radius_list_nonnegative THEN
      ASM_REWRITE_TAC[];
      USE_THEN "hessian_contains" ACCEPT_TAC;
      ASM_REWRITE_TAC[candle_q_radius_list_length;
                      LENGTH_LIST_OF_SEQ];
      REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
      ASM_SIMP_TAC[candle_q_radius_list_length;
                   EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]];
    ASM_SIMP_TAC[candle_q_weighted_rows_list_of_seq_sum]]);;

let candle_poly_m_taylor_error_sound = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     m_taylor_error
       (candle_poly_denote_dim e)
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_radius_vector boxes)
       (candle_q_real
         (candle_q_weighted_rows_abs_upper
           (candle_q_radius_list boxes)
           (candle_q_radius_list boxes)
           (candle_q_program_interval_matrix boxes
             (candle_poly_hessian_programs (dimindex (:N)) e))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[m_taylor_error] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM partial2] THEN
  MATCH_MP_TAC candle_poly_hessian_taylor_sum_bound THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE hessian_bound";;

let candle_q_dim_whole_box_upper_real = prove
 (`!pf pds pdds boxes.
     candle_q_real
       (candle_q_dim_whole_box_upper pf pds pdds boxes) =
     candle_q_real
       (SND
         (candle_q_program_interval
           (candle_q_center_environment_list boxes) pf)) +
     candle_q_real
       (candle_q_dot_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_program_interval_list
           (candle_q_center_environment_list boxes) pds)) +
     inv (&2) *
     candle_q_real
       (candle_q_weighted_rows_abs_upper
         (candle_q_radius_list boxes)
         (candle_q_radius_list boxes)
         (candle_q_program_interval_matrix boxes pdds))`,
  REWRITE_TAC[candle_q_dim_whole_box_upper_def;
              candle_q_dim_taylor_upper_def;
              candle_q_real_add; candle_q_real_mul;
              candle_q_real_half] THEN
  REAL_ARITH_TAC);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE upper_real";;

let candle_poly_dim_whole_box_accept_sound = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_poly_dim_whole_box_accept e boxes
     ==>
     !p. p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_poly_denote_dim e (p:real^N) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`e:candle_poly_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`]
     candle_poly_dim_whole_box_accept_components) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "valid")
     (CONJUNCTS_THEN2 (LABEL_TAC "inputs_valid")
       (CONJUNCTS_THEN2
         (LABEL_TAC "boxes_valid") (LABEL_TAC "upper_negative_q")))) THEN
  SUBGOAL_THEN
   `candle_q_real
      (candle_q_dim_whole_box_upper
        (candle_poly_compile e)
        (candle_poly_gradient_programs (dimindex (:N)) e)
        (candle_poly_hessian_programs (dimindex (:N)) e)
        boxes) < &0`
   (LABEL_TAC "upper_negative") THENL
   [USE_THEN "upper_negative_q"
     (fun th ->
       ACCEPT_TAC
        (REWRITE_RULE[candle_q_le_real; candle_q_dim_real_zero;
                      REAL_NOT_LE] th));
    ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `candle_q_real
      (candle_q_dim_whole_box_upper
        (candle_poly_compile e)
        (candle_poly_gradient_programs (dimindex (:N)) e)
        (candle_poly_hessian_programs (dimindex (:N)) e)
        boxes)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m_cell_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_center_vector boxes)
       (candle_q_box_radius_vector boxes)`
     (LABEL_TAC "cell_domain") THENL
     [MATCH_MP_TAC candle_q_box_m_cell_domain THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `diff2_domain
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_poly_denote_dim e)`
     (LABEL_TAC "diff2") THENL
     [REWRITE_TAC[diff2_domain] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC diff2c_imp_diff2 THEN
      MATCH_MP_TAC candle_poly_denote_dim_diff2c THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `m_taylor_error
       (candle_poly_denote_dim e)
       (candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes : real^N)
       (candle_q_box_radius_vector boxes)
       (candle_q_real
         (candle_q_weighted_rows_abs_upper
           (candle_q_radius_list boxes)
           (candle_q_radius_list boxes)
           (candle_q_program_interval_matrix boxes
             (candle_poly_hessian_programs (dimindex (:N)) e))))`
     (LABEL_TAC "taylor_error") THENL
     [MATCH_MP_TAC candle_poly_m_taylor_error_sound THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_poly_denote_dim e
        (candle_q_box_center_vector boxes : real^N) <=
      candle_q_real
        (SND
          (candle_q_program_interval
            (candle_q_center_environment_list boxes)
            (candle_poly_compile e)))`
     (LABEL_TAC "center_bound") THENL
     [MP_TAC
       (SPECL
         [`e:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`]
         candle_poly_center_interval_contains) THEN
      ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_real
        (SND
          (candle_q_program_interval
            (candle_q_center_environment_list boxes)
            (candle_poly_compile e))) +
      sum (1..dimindex (:N))
        (\i. (candle_q_box_radius_vector boxes : real^N)$i *
             abs
               (partial i (candle_poly_denote_dim e)
                 (candle_q_box_center_vector boxes : real^N))) +
      candle_q_real
        (candle_q_weighted_rows_abs_upper
          (candle_q_radius_list boxes)
          (candle_q_radius_list boxes)
          (candle_q_program_interval_matrix boxes
            (candle_poly_hessian_programs (dimindex (:N)) e))) / &2 <=
      candle_q_real
        (candle_q_dim_whole_box_upper
          (candle_poly_compile e)
          (candle_poly_gradient_programs (dimindex (:N)) e)
          (candle_poly_hessian_programs (dimindex (:N)) e)
          boxes)`
     (LABEL_TAC "computed_upper_bound") THENL
     [MP_TAC
       (SPECL
         [`e:candle_poly_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`]
         candle_poly_gradient_taylor_sum_bound) THEN
      ASM_REWRITE_TAC[candle_q_dim_whole_box_upper_real;
                      real_div] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC
     (ISPECL
       [`((candle_q_box_lower_vector boxes : real^N),
          (candle_q_box_upper_vector boxes : real^N))`;
        `(candle_q_box_center_vector boxes : real^N)`;
        `(candle_q_box_radius_vector boxes : real^N)`;
        `(candle_poly_denote_dim e : real^N->real)`;
        `candle_q_real
          (candle_q_weighted_rows_abs_upper
            (candle_q_radius_list boxes)
            (candle_q_radius_list boxes)
            (candle_q_program_interval_matrix boxes
              (candle_poly_hessian_programs (dimindex (:N)) e)))`;
        `candle_q_real
          (SND
            (candle_q_program_interval
              (candle_q_center_environment_list boxes)
              (candle_poly_compile e)))`;
        `candle_q_real
          (candle_q_dim_whole_box_upper
            (candle_poly_compile e)
            (candle_poly_gradient_programs (dimindex (:N)) e)
            (candle_poly_hessian_programs (dimindex (:N)) e)
            boxes)`]
       m_taylor_upper_bound) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `p:real^N`) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "upper_negative" ACCEPT_TAC]);;

let _ = print_endline "CANDLE_DIM_SOUND_STAGE final_acceptance";;

end;;
