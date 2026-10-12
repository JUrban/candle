(* ========================================================================== *)
(* Historical center jet: direct arithmetic contains the analytic reference. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_first_order_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_reference_sound = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound;;

let candle_fs_hist_direct_lookups_contain = prove
 (`!environment (values:num->real).
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6)
     ==> !coordinate. coordinate < 6
          ==> candle_fs_interval_contains
                (candle_fs_interval_lookup coordinate environment)
                (values coordinate)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_delta_x4_value_direct_contains = prove
 (`!environment (values:num->real).
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6)
     ==> candle_fs_interval_contains
           (candle_fs_hist_delta_x4_value_direct environment)
           (candle_fs_hist_delta_x4_real values)`,
  REPEAT STRIP_TAC THEN
  let lookup_tac =
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC in
  let signed_lookup_tac =
    FIRST
     [MATCH_MP_TAC candle_fs_interval_neg_sound THEN lookup_tac;
      lookup_tac] in
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_neg (candle_fs_interval_lookup 0 environment);
         candle_fs_interval_lookup 1 environment;
         candle_fs_interval_lookup 2 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 3 environment);
         candle_fs_interval_lookup 4 environment;
         candle_fs_interval_lookup 5 environment])
      (ITLIST (\x total:real. x + total)
        [--(values 0);values 1;values 2;
         --(values 3);values 4;values 5] (&0))`
  (LABEL_TAC "linear") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_value_direct_def;
              candle_fs_hist_delta_x4_real_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac;
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac;
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac;
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac;
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac;
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [lookup_tac;
      USE_THEN "linear" ACCEPT_TAC]]);;

let candle_fs_angle_delta_value_contains = prove
 (`!environment (values:num->real).
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6)
     ==> candle_fs_interval_contains
           (candle_fs_angle_delta_value environment)
           (candle_fs_hist_delta_real values)`,
  REPEAT STRIP_TAC THEN
  let lookup_tac =
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC in
  let signed_lookup_tac =
    FIRST
     [MATCH_MP_TAC candle_fs_interval_neg_sound THEN lookup_tac;
      lookup_tac] in
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_neg (candle_fs_interval_lookup 0 environment);
         candle_fs_interval_lookup 1 environment;
         candle_fs_interval_lookup 2 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 3 environment);
         candle_fs_interval_lookup 4 environment;
         candle_fs_interval_lookup 5 environment])
      (ITLIST (\x total:real. x + total)
        [--(values 0);values 1;values 2;
         --(values 3);values 4;values 5] (&0))`
  (LABEL_TAC "l0") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_lookup 0 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 1 environment);
         candle_fs_interval_lookup 2 environment;
         candle_fs_interval_lookup 3 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 4 environment);
         candle_fs_interval_lookup 5 environment])
      (ITLIST (\x total:real. x + total)
        [values 0;--(values 1);values 2;values 3;
         --(values 4);values 5] (&0))`
  (LABEL_TAC "l1") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_lookup 0 environment;
         candle_fs_interval_lookup 1 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 2 environment);
         candle_fs_interval_lookup 3 environment;
         candle_fs_interval_lookup 4 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 5 environment)])
      (ITLIST (\x total:real. x + total)
        [values 0;values 1;--(values 2);values 3;values 4;
         --(values 5)] (&0))`
  (LABEL_TAC "l2") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_angle_delta_value_def;
              candle_fs_hist_delta_real_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l0" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l1" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l2" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac]]);;

let candle_fs_angle_delta_gradient_contains = prove
 (`!environment (values:num->real).
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6)
     ==> ALL2 candle_fs_interval_contains
           (candle_fs_angle_delta_gradient environment)
           (candle_fs_hist_delta_gradient_real values)`,
  REPEAT STRIP_TAC THEN
  let lookup_tac =
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC in
  let product_tac =
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THEN lookup_tac in
  let atom_tac =
    FIRST
     [MATCH_MP_TAC candle_fs_hist_scale_neg_two_contains THEN product_tac;
      MATCH_MP_TAC candle_fs_interval_neg_sound THEN product_tac;
      product_tac] in
  REWRITE_TAC[candle_fs_angle_delta_gradient_def;
              candle_fs_hist_delta_gradient_real_def;
              LET_DEF; LET_END_DEF; ALL2] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THEN atom_tac);;

let candle_fs_hist_root_delta_gradient_direct_contains = prove
 (`!environment (values:num->real) root_lower root_upper.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6) /\
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_delta_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fsn_interval_list_scale
         (candle_fs_hist_positive_inv
           (candle_fs_angle_interval_scale 2
             ((root_lower,0),(root_upper,0))))
         (candle_fs_angle_delta_gradient environment))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND] THEN
  REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
  REWRITE_TAC[GSYM candle_fs_hist_inv_twice_positive_def] THEN
  REWRITE_TAC[GSYM candle_fs_hist_positive_sqrt_gradient_def] THEN
  MATCH_MP_TAC candle_fs_hist_positive_sqrt_gradient_universal_contains THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM candle_fs_hist_delta_gradient_real_list_of_seq] THEN
  MATCH_MP_TAC candle_fs_angle_delta_gradient_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_b_gradient_direct_contains = prove
 (`!environment (values:num->real)
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6) /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_b_gradient
         ((root_four_x0_lower,0),(root_four_x0_upper,0))
         ((root_delta_lower,0),(root_delta_upper,0))
         (candle_fsn_interval_list_scale
           (candle_fs_hist_positive_inv
             (candle_fs_angle_interval_scale 2
               ((root_delta_lower,0),(root_delta_upper,0))))
           (candle_fs_angle_delta_gradient environment))
         (candle_fs_angle_interval_mul
           (candle_fs_angle_interval_scale 2 candle_fs_interval_one)
           (candle_fs_hist_positive_inv
             ((root_four_x0_lower,0),(root_four_x0_upper,0)))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_b_gradient_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_root_delta_gradient_direct_contains THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM candle_fs_hist_two_over_positive_root_def] THEN
    MATCH_MP_TAC candle_fs_hist_two_over_positive_root_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_c_vector_direct_contains = prove
 (`!environment (values:num->real)
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6) /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_c_vector
         (candle_fs_hist_delta_x4_value_direct environment)
         (candle_fs_angle_interval_mul
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))
         (candle_fs_hist_delta_x4_gradient environment)
         (candle_fs_hist_b_gradient
           ((root_four_x0_lower,0),(root_four_x0_upper,0))
           ((root_delta_lower,0),(root_delta_upper,0))
           (candle_fsn_interval_list_scale
             (candle_fs_hist_positive_inv
               (candle_fs_angle_interval_scale 2
                 ((root_delta_lower,0),(root_delta_upper,0))))
             (candle_fs_angle_delta_gradient environment))
           (candle_fs_angle_interval_mul
             (candle_fs_angle_interval_scale 2 candle_fs_interval_one)
             (candle_fs_hist_positive_inv
               ((root_four_x0_lower,0),(root_four_x0_upper,0))))))
       (list_of_seq (candle_fs_hist_c_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_c_vector_contains THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_hist_delta_x4_gradient_def;
                LET_DEF; LET_END_DEF; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ONCE_REWRITE_TAC[GSYM candle_fs_hist_delta_x4_gradient_real_list_of_seq] THEN
    MATCH_MP_TAC candle_fs_hist_delta_x4_gradient_contains THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_b_gradient_length];
    MATCH_MP_TAC candle_fs_hist_b_gradient_direct_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_delta_x4_value_direct_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_b_value_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_first_order_direct_reference_value_contains = prove
 (`!environment (values:num->real)
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6) /\
     root_delta_lower <= root_delta_upper /\
     root_four_x0_lower <= root_four_x0_upper /\
     0 < (root_delta_lower * root_four_x0_lower) DIV candle_fs_scale /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     -- &1 < candle_fs_real
       (FST
         (candle_fs_hist_quotient
           (candle_fs_hist_delta_x4_value_direct environment)
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))) /\
     candle_fs_real
       (SND
         (candle_fs_hist_quotient
           (candle_fs_hist_delta_x4_value_direct environment)
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))) < &1
     ==> candle_fs_interval_contains
       (candle_fs_first_value
         (candle_fs_hist_first_order_direct environment
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_first_order_direct_def;
              candle_fs_first_value_def;
              candle_fs_first_make_def;
              LET_DEF; LET_END_DEF; FST] THEN
  REWRITE_TAC[GSYM candle_fs_hist_positive_product_inv_def] THEN
  REWRITE_TAC[GSYM candle_fs_hist_quotient_def] THEN
  REWRITE_TAC[GSYM candle_fs_hist_dihedral_value_from_quotient_def] THEN
  ONCE_REWRITE_TAC[candle_fs_hist_reference_dihedral_value] THEN
  MATCH_MP_TAC candle_fs_hist_dihedral_value_sound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_delta_x4_value_direct_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_first_order_direct_reference_gradient_contains = prove
 (`!environment (values:num->real)
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper
      u126_lower u126_upper u135_lower u135_upper.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6) /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     0 < root_four_x0_lower /\ root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     FST (candle_fs_hist_u126 environment) =
       ((u126_lower,0),(u126_upper,0)) /\
     FST (candle_fs_hist_u135 environment) =
       ((u135_lower,0),(u135_upper,0)) /\
     u126_lower <= u126_upper /\
     u135_lower <= u135_upper /\
     0 < (u126_lower * u135_lower) DIV candle_fs_scale /\
     candle_fs_interval_contains (FST (candle_fs_hist_u126 environment))
       (candle_fs_hist_u126_real values) /\
     candle_fs_interval_contains (FST (candle_fs_hist_u135 environment))
       (candle_fs_hist_u135_real values)
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient
         (candle_fs_hist_first_order_direct environment
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_first_order_direct_def;
              candle_fs_first_gradient_def;
              candle_fs_first_make_def;
              LET_DEF; LET_END_DEF; SND] THEN
  MATCH_MP_TAC candle_fs_hist_final_gradient_reference_contains THEN
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fs_hist_c_vector_length;
    MATCH_MP_TAC candle_fs_hist_c_vector_direct_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`environment:((num#num)#(num#num))list`; `values:num->real`;
        `u126_lower:num`; `u126_upper:num`;
        `u135_lower:num`; `u135_upper:num`]
       candle_fs_hist_reciprocal_u_fixed_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_special_gradient_fixed_contains THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

end;;
