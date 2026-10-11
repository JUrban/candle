(* ========================================================================== *)
(* Historical low-work dihedral: discharge production source contracts.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_assembler_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_assembler_sound;;

(* Scalar production boundary: the historical quotient/atan instruction
   encloses the value of the same analytic jet, using only authenticated box
   and supplied-root contracts. *)

let candle_fs_hist_second_order_reference_value_contains = prove
 (`!boxes values root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
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
     ==> candle_fs_interval_contains
       (candle_fs_hist_second_value
         (candle_fs_hist_second_order boxes
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[candle_fs_hist_second_value_def]) THEN
  REWRITE_TAC[candle_fs_hist_second_order_def;
              candle_fs_hist_second_value_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  ONCE_REWRITE_TAC[candle_fs_hist_reference_dihedral_value] THEN
  MATCH_MP_TAC
   (SPECL
     [`FST
        (candle_fs_hist_delta_x4_second
          (boxes:((num#num)#(num#num))list))`;
      `root_delta_lower:num`; `root_delta_upper:num`;
      `root_four_x0_lower:num`; `root_four_x0_upper:num`;
      `candle_fs_hist_delta_x4_real (values:num->real)`;
      `sqrt (candle_fs_hist_delta_real (values:num->real))`;
      `sqrt (candle_fs_hist_four_x0_real (values:num->real))`]
     candle_fs_hist_dihedral_value_sound) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM candle_fs_hist_second_value_def] THEN
  MATCH_MP_TAC candle_fs_hist_delta_x4_second_value_contains THEN
  ASM_REWRITE_TAC[]);;

end;;
