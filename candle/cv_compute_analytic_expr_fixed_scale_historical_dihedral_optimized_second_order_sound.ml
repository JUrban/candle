(* ========================================================================== *)
(* Historical low-work dihedral: package the complete optimized real jet.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound;;

(* This constructor lemma is the final representation boundary.  Once the
   three executable payloads enclose one real jet, their historical record is
   a jet accepted by the universal rational checker. *)

let candle_fs_hist_second_components_from_data = prove
 (`!second value gradient hessian_value.
     LENGTH (candle_fs_hist_second_gradient second) = 6 /\
     LENGTH (candle_fs_hist_second_hessian second) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_second_hessian second) /\
     candle_fs_interval_contains
       (candle_fs_hist_second_value second) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_hist_second_gradient second)
       (list_of_seq gradient 6) /\
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian second)
       (list_of_seq (\i. list_of_seq (hessian_value i) 6) 6)
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q second)
       value gradient hessian_value`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  ASM_REWRITE_TAC[candle_fs_first_to_q_shape;
                  candle_fs_first_make_def;
                  candle_fs_first_value_def;
                  candle_fs_first_gradient_def; FST; SND]);;

(* The scalar denoted by the reference analytic jet is exactly the scalar
   enclosed by the historical quotient/arctangent instruction. *)

let candle_fs_hist_reference_dihedral_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_reference_dihedral_real_jet values) =
     pi / &2 +
       atn
         (--(candle_fs_hist_delta_x4_real values) *
          inv
            (sqrt (candle_fs_hist_delta_real values) *
             sqrt (candle_fs_hist_four_x0_real values)))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_real_hist_dihedral_jet_def;
              candle_fs_hist_delta_x4_real_jet_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_add_def;
              candle_hist_real_jet_pi_half_def;
              candle_hist_real_jet_atn_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_neg_def;
              candle_hist_real_jet_inv_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def; FST; SND]);;

(* The historical instruction replaces gradient coordinate three by the
   smaller square-root quotient.  This is not an approximation: on the
   positive dihedral domain it is exactly the low-work analytic gradient. *)

let candle_fs_hist_special_gradient_real_is_low_work = prove
 (`!values.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==> sqrt (candle_fs_hist_four_x0_real values) *
           inv (&2 * sqrt (candle_fs_hist_delta_real values)) =
         inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values) *
         candle_fs_hist_c_real values 3`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sqrt (candle_fs_hist_delta_real values) *
      sqrt (candle_fs_hist_delta_real values) =
    candle_fs_hist_delta_real values`
  (LABEL_TAC "root_delta_square") THENL
   [MP_TAC
      (SPEC `candle_fs_hist_delta_real (values:num->real)` SQRT_POW_2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(sqrt (candle_fs_hist_delta_real values) = &0)`
  (LABEL_TAC "root_delta_nonzero") THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    ASM_SIMP_TAC[SQRT_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(candle_fs_hist_u126_real values *
      candle_fs_hist_u135_real values = &0)`
  (LABEL_TAC "u_product_nonzero") THENL
   [REWRITE_TAC[candle_fs_hist_u_product_identity] THEN
    SUBGOAL_THEN
     `&0 < (values:num->real) 0`
    ASSUME_TAC THENL
     [UNDISCH_TAC
        `&0 < candle_fs_hist_four_x0_real (values:num->real)` THEN
      REWRITE_TAC[candle_fs_hist_four_x0_real_def] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      MATCH_ACCEPT_TAC
        (SPEC `candle_fs_hist_delta_x4_real (values:num->real)`
          REAL_LE_SQUARE)];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_c_real_def;
              candle_fs_hist_delta_x4_derivative_def;
              candle_fs_hist_b_real_jet_value;
              candle_fs_hist_b_gradient_target_eq;
              candle_fs_hist_b_gradient_target_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_delta_gradient_3_is_delta_x4;
              candle_fs_hist_u_product_identity;
              candle_fs_hist_four_x0_real_def;
              FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REMOVE_THEN "root_delta_square" MP_TAC THEN
  REMOVE_THEN "root_delta_nonzero" MP_TAC THEN
  REMOVE_THEN "u_product_nonzero" MP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_product_identity] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_hist_replace_three_contains = prove
 (`!items value (values:num->real).
     LENGTH items = 6 /\
     ALL2 candle_fs_interval_contains items (list_of_seq values 6) /\
     candle_fs_interval_contains value (values 3)
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_replace_three items value)
       (list_of_seq values 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_replace_three_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[ALL2] THEN
  let lookup_tac index =
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`6`; `items:((num#num)#(num#num))list`;
           `values:num->real`; index]
          candle_fs_hist_interval_lookup_contains)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV in
  REPEAT CONJ_TAC THENL
   [lookup_tac `0`;
    lookup_tac `1`;
    lookup_tac `2`;
    ASM_REWRITE_TAC[];
    lookup_tac `4`;
    lookup_tac `5`]);;

let candle_fs_hist_scaled_c_contains = prove
 (`!values c reciprocal_u.
     ALL2 candle_fs_interval_contains c
       (list_of_seq (candle_fs_hist_c_real values) 6) /\
     candle_fs_interval_contains reciprocal_u
       (inv
         (candle_fs_hist_u126_real values *
          candle_fs_hist_u135_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fsn_interval_list_scale reciprocal_u c)
       (list_of_seq
         (\i. inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values) *
           candle_fs_hist_c_real values i) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
   (REWRITE_RULE[candle_map_scale_list_of_seq]
     (SPECL
       [`reciprocal_u:((num#num)#(num#num))`;
        `inv
          (candle_fs_hist_u126_real (values:num->real) *
           candle_fs_hist_u135_real values)`;
        `c:((num#num)#(num#num))list`;
        `list_of_seq (candle_fs_hist_c_real values) 6`]
       candle_fsn_interval_list_scale_contains)) THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_final_gradient_low_work_contains = prove
 (`!values c reciprocal_u special_gradient.
     LENGTH c = 6 /\
     ALL2 candle_fs_interval_contains c
       (list_of_seq (candle_fs_hist_c_real values) 6) /\
     candle_fs_interval_contains reciprocal_u
       (inv
         (candle_fs_hist_u126_real values *
          candle_fs_hist_u135_real values)) /\
     candle_fs_interval_contains special_gradient
       (sqrt (candle_fs_hist_four_x0_real values) *
        inv (&2 * sqrt (candle_fs_hist_delta_real values))) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_replace_three
         (candle_fsn_interval_list_scale reciprocal_u c)
         special_gradient)
       (list_of_seq
         (\i. inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values) *
           candle_fs_hist_c_real values i) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains special_gradient
      (inv
        (candle_fs_hist_u126_real values *
         candle_fs_hist_u135_real values) *
       candle_fs_hist_c_real values 3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sqrt (candle_fs_hist_four_x0_real values) *
        inv (&2 * sqrt (candle_fs_hist_delta_real values)) =
      inv
        (candle_fs_hist_u126_real values *
         candle_fs_hist_u135_real values) *
      candle_fs_hist_c_real values 3`
    (LABEL_TAC "special_gradient_eq") THENL
     [MATCH_MP_TAC
       (SPEC `values:num->real`
         candle_fs_hist_special_gradient_real_is_low_work) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "special_gradient_eq"
       (fun equality -> ONCE_REWRITE_TAC[GSYM equality]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC
   (SPECL
     [`candle_fsn_interval_list_scale reciprocal_u c`;
      `special_gradient:((num#num)#(num#num))`;
      `\i. inv
        (candle_fs_hist_u126_real (values:num->real) *
         candle_fs_hist_u135_real values) *
        candle_fs_hist_c_real values i`]
     candle_fs_hist_replace_three_contains) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_fsn_interval_list_scale_length];
    MATCH_MP_TAC
     (SPECL
       [`values:num->real`; `c:((num#num)#(num#num))list`;
        `reciprocal_u:((num#num)#(num#num))`]
       candle_fs_hist_scaled_c_contains) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_final_gradient_reference_contains = prove
 (`!values c reciprocal_u special_gradient.
     LENGTH c = 6 /\
     ALL2 candle_fs_interval_contains c
       (list_of_seq (candle_fs_hist_c_real values) 6) /\
     candle_fs_interval_contains reciprocal_u
       (inv
         (candle_fs_hist_u126_real values *
          candle_fs_hist_u135_real values)) /\
     candle_fs_interval_contains special_gradient
       (sqrt (candle_fs_hist_four_x0_real values) *
        inv (&2 * sqrt (candle_fs_hist_delta_real values))) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_replace_three
         (candle_fsn_interval_list_scale reciprocal_u c)
         special_gradient)
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_hist_replace_three
        (candle_fsn_interval_list_scale reciprocal_u c)
        special_gradient)
      (list_of_seq
        (\i. inv
          (candle_fs_hist_u126_real values *
           candle_fs_hist_u135_real values) *
          candle_fs_hist_c_real values i) 6)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_final_gradient_low_work_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `list_of_seq
      (\i. inv
        (candle_fs_hist_u126_real values *
         candle_fs_hist_u135_real values) *
        candle_fs_hist_c_real values i) 6 =
    list_of_seq
      (candle_hist_real_jet_gradient
        (candle_fs_hist_reference_dihedral_real_jet values)) 6`
  (fun list_eq -> ASM_REWRITE_TAC[GSYM list_eq]) THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_fs_hist_reference_dihedral_gradient_is_low_work]);;

let candle_fs_hist_c_vector_length = prove
 (`!delta_x4_value b delta_x4_gradient b_gradient.
     LENGTH
       (candle_fs_hist_c_vector delta_x4_value b
         delta_x4_gradient b_gradient) = 6`,
  REWRITE_TAC[candle_fs_hist_c_vector_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_special_gradient_fixed_contains = prove
 (`!values root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     0 < root_delta_lower /\
     root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> candle_fs_interval_contains
       (candle_fs_angle_interval_mul
         ((root_four_x0_lower,0),(root_four_x0_upper,0))
         (candle_fs_hist_positive_inv
           (candle_fs_angle_interval_scale 2
             ((root_delta_lower,0),(root_delta_upper,0)))))
       (sqrt (candle_fs_hist_four_x0_real values) *
        inv (&2 * sqrt (candle_fs_hist_delta_real values)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_positive_inv_double_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_reciprocal_u_fixed_contains = prove
 (`!boxes values u126_lower u126_upper u135_lower u135_upper.
     FST (candle_fs_hist_u126 boxes) =
       ((u126_lower,0),(u126_upper,0)) /\
     FST (candle_fs_hist_u135 boxes) =
       ((u135_lower,0),(u135_upper,0)) /\
     u126_lower <= u126_upper /\
     u135_lower <= u135_upper /\
     0 < (u126_lower * u135_lower) DIV candle_fs_scale /\
     candle_fs_interval_contains (FST (candle_fs_hist_u126 boxes))
       (candle_fs_hist_u126_real values) /\
     candle_fs_interval_contains (FST (candle_fs_hist_u135 boxes))
       (candle_fs_hist_u135_real values)
     ==> candle_fs_interval_contains
       (candle_fs_hist_positive_inv
         (candle_fs_angle_interval_mul
           (FST (candle_fs_hist_u126 boxes))
           (FST (candle_fs_hist_u135 boxes))))
       (inv
         (candle_fs_hist_u126_real values *
          candle_fs_hist_u135_real values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      ((u126_lower,0),(u126_upper,0))
      (candle_fs_hist_u126_real values)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      ((u135_lower,0),(u135_upper,0))
      (candle_fs_hist_u135_real values)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM candle_fs_hist_positive_product_inv_def] THEN
  MATCH_MP_TAC
   (SPECL
     [`u126_lower:num`; `u126_upper:num`;
      `u135_lower:num`; `u135_upper:num`;
      `candle_fs_hist_u126_real (values:num->real)`;
      `candle_fs_hist_u135_real (values:num->real)`]
     candle_fs_hist_positive_product_inv_contains) THEN
  ASM_REWRITE_TAC[]);;

end;;
