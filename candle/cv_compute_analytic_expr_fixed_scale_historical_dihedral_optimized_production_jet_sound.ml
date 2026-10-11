(* ========================================================================== *)
(* Historical low-work dihedral: assemble the production jet contract.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_production_hessian_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_jet_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_assembler_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_hessian_sound;;

(* The three independently proved production boundaries are sufficient for
   the single reflected jet contract consumed by the Taylor checker. *)

let candle_fs_hist_second_order_reference_jet_contains = prove
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
     0 < (root_delta_lower * root_four_x0_lower) DIV candle_fs_scale /\
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
       (FST (candle_fs_interval_lookup 5 boxes)) /\
     -- &1 < candle_fs_real
       (FST
         (candle_fs_hist_quotient
           (candle_fs_hist_second_value
             (candle_fs_hist_delta_x4_second boxes))
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))) /\
     candle_fs_real
       (SND
         (candle_fs_hist_quotient
           (candle_fs_hist_second_value
             (candle_fs_hist_delta_x4_second boxes))
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))) < &1
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_order boxes
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_second_order_reference_from_components THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `root_delta_lower:num`; `root_delta_upper:num`;
        `root_four_x0_lower:num`; `root_four_x0_upper:num`]
       candle_fs_hist_second_order_reference_value_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `root_delta_lower:num`; `root_delta_upper:num`;
        `root_four_x0_lower:num`; `root_four_x0_upper:num`;
        `u126_lower:num`; `u126_upper:num`;
        `u135_lower:num`; `u135_upper:num`]
       candle_fs_hist_second_order_reference_gradient_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`boxes:((num#num)#(num#num))list`; `values:num->real`;
        `delta_lower:num`; `delta_upper:num`;
        `root_delta_lower:num`; `root_delta_upper:num`;
        `root_four_x0_lower:num`; `root_four_x0_upper:num`;
        `x0_lower:num`; `x0_upper:num`;
        `u126_lower:num`; `u126_upper:num`;
        `u135_lower:num`; `u135_upper:num`]
       candle_fs_hist_second_order_reference_hessian_contains) THEN
    ASM_REWRITE_TAC[]]);;

end;;
