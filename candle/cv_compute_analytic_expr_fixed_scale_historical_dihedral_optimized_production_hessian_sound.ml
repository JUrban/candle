(* ========================================================================== *)
(* Historical low-work dihedral: discharge the production Hessian contract.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_production_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_hessian_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_sound;;

let candle_fs_hist_b_hessian_shape = prove
 (`!root_four_x0 root_delta_value root_delta_gradient
      root_delta_hessian two_over_root_four_x0 x0.
     LENGTH
       (candle_fs_hist_b_hessian root_four_x0 root_delta_value
         root_delta_gradient root_delta_hessian
         two_over_root_four_x0 x0) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_b_hessian root_four_x0 root_delta_value
         root_delta_gradient root_delta_hessian
         two_over_root_four_x0 x0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_b_hessian_def;
              candle_fs_hist_b_hessian_row_def;
              LET_DEF; LET_END_DEF; LENGTH; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_result_gradient_length = prove
 (`!items value.
     LENGTH (candle_fs_hist_replace_three items value) = 6`,
  REWRITE_TAC[candle_fs_hist_replace_three_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_log_u_gradient_length = prove
 (`!u126_gradient reciprocal_u126 u135_gradient reciprocal_u135.
     LENGTH
       (candle_fs_hist_log_u_gradient u126_gradient reciprocal_u126
         u135_gradient reciprocal_u135) = 6`,
  REWRITE_TAC[candle_fs_hist_log_u_gradient_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_second_order_reference_hessian_contains = prove
 (`!boxes values delta_lower delta_upper
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper
      x0_lower x0_upper
      u126_lower u126_upper u135_lower u135_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value (candle_fs_hist_delta_second boxes) =
       ((delta_lower,0),(delta_upper,0)) /\
     0 < delta_lower /\ delta_lower <= delta_upper /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_interval_lookup 0 boxes = ((x0_lower,0),(x0_upper,0)) /\
     0 < x0_lower /\ x0_lower <= x0_upper /\
     FST (candle_fs_hist_u126 boxes) =
       ((u126_lower,0),(u126_upper,0)) /\
     FST (candle_fs_hist_u135 boxes) =
       ((u135_lower,0),(u135_upper,0)) /\
     0 < u126_lower /\ u126_lower <= u126_upper /\
     0 < u135_lower /\ u135_lower <= u135_upper /\
     0 < (u126_lower * u135_lower) DIV candle_fs_scale /\
     candle_fs_interval_contains (FST (candle_fs_hist_u126 boxes))
       (candle_fs_hist_u126_real values) /\
     candle_fs_interval_contains (FST (candle_fs_hist_u135 boxes))
       (candle_fs_hist_u135_real values) /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 1 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 2 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 4 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 5 boxes))
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order boxes
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_order_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_MP_TAC
   (CONV_RULE (DEPTH_CONV ETA_CONV)
     candle_fs_hist_final_hessian_reference_contains) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_b_value_contains THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
                candle_hist_real_jet_value_def;
                candle_hist_real_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_value_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC
     (CONJUNCT1
       (SPEC `boxes:((num#num)#(num#num))list`
         candle_fs_hist_delta_x4_second_data_shape));
    REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
                candle_hist_real_jet_gradient_def;
                candle_hist_real_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_gradient_contains THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_delta_x4_second
           (boxes:((num#num)#(num#num))list)`
         candle_fs_hist_second_hessian_def)] THEN
    MATCH_ACCEPT_TAC
     (CONJUNCT1
       (CONJUNCT2
         (SPEC `boxes:((num#num)#(num#num))list`
           candle_fs_hist_delta_x4_second_data_shape)));
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_delta_x4_second
           (boxes:((num#num)#(num#num))list)`
         candle_fs_hist_second_hessian_def)] THEN
    MATCH_ACCEPT_TAC
     (CONJUNCT2
       (CONJUNCT2
         (SPEC `boxes:((num#num)#(num#num))list`
           candle_fs_hist_delta_x4_second_data_shape)));
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_delta_x4_second
           (boxes:((num#num)#(num#num))list)`
         candle_fs_hist_second_hessian_def)] THEN
    REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
                candle_hist_real_jet_hessian_def;
                candle_hist_real_jet_make_def; FST; SND] THEN
    MATCH_ACCEPT_TAC
     (CONV_RULE (DEPTH_CONV ETA_CONV)
       candle_fs_hist_delta_x4_second_hessian_contains);
    MATCH_ACCEPT_TAC candle_fs_hist_b_gradient_length;
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second
             (boxes:((num#num)#(num#num))list))
           ((root_delta_lower,0),(root_delta_upper,0))`
         candle_fs_hist_second_gradient_def)] THEN
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `root_delta_lower:num`; `root_delta_upper:num`;
        `root_four_x0_lower:num`; `root_four_x0_upper:num`]
       candle_fs_hist_b_gradient_fixed_contains) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_b_hessian_def;
                LET_DEF; LET_END_DEF; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[candle_fs_hist_b_hessian_def;
                candle_fs_hist_b_hessian_row_def;
                LET_DEF; LET_END_DEF; ALL; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second
             (boxes:((num#num)#(num#num))list))
           ((root_delta_lower,0),(root_delta_upper,0))`
         candle_fs_hist_second_gradient_def)] THEN
    ONCE_REWRITE_TAC
     [GSYM
       (ISPEC
         `candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second
             (boxes:((num#num)#(num#num))list))
           ((root_delta_lower,0),(root_delta_upper,0))`
         candle_fs_hist_second_hessian_def)] THEN
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `delta_lower:num`; `delta_upper:num`;
        `root_delta_lower:num`; `root_delta_upper:num`;
        `root_four_x0_lower:num`; `root_four_x0_upper:num`;
        `x0_lower:num`; `x0_upper:num`]
       candle_fs_hist_b_hessian_fixed_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `u126_lower:num`; `u126_upper:num`;
        `u135_lower:num`; `u135_upper:num`]
       candle_fs_hist_reciprocal_u_fixed_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC candle_fs_hist_result_gradient_length;
    MATCH_MP_TAC candle_fs_hist_final_gradient_low_work_contains THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_fs_hist_c_vector_length;
      ONCE_REWRITE_TAC
       [GSYM
         (ISPEC
           `candle_fs_hist_delta_x4_second
             (boxes:((num#num)#(num#num))list)`
           candle_fs_hist_second_value_def)] THEN
      ONCE_REWRITE_TAC
       [GSYM
         (ISPEC
           `candle_fs_hist_delta_x4_second
             (boxes:((num#num)#(num#num))list)`
           candle_fs_hist_second_gradient_def)] THEN
      ONCE_REWRITE_TAC
       [GSYM
         (ISPEC
           `candle_fs_hist_second_sqrt_supplied
             (candle_fs_hist_delta_second
               (boxes:((num#num)#(num#num))list))
             ((root_delta_lower,0),(root_delta_upper,0))`
           candle_fs_hist_second_gradient_def)] THEN
      MATCH_MP_TAC
       (SPECL
         [`boxes:((num#num)#(num#num))list`; `values:num->real`;
          `root_delta_lower:num`; `root_delta_upper:num`;
          `root_four_x0_lower:num`; `root_four_x0_upper:num`]
         candle_fs_hist_c_vector_fixed_contains) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
       (SPECL
         [`boxes:((num#num)#(num#num))list`; `values:num->real`;
          `u126_lower:num`; `u126_upper:num`;
          `u135_lower:num`; `u135_upper:num`]
         candle_fs_hist_reciprocal_u_fixed_contains) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_hist_special_gradient_fixed_contains THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_ACCEPT_TAC candle_fs_hist_log_u_gradient_length;
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `u126_lower:num`; `u126_upper:num`;
        `u135_lower:num`; `u135_upper:num`]
       candle_fs_hist_log_u_gradient_fixed_from_boxes_contains) THEN
    ASM_REWRITE_TAC[]]);;

end;;
