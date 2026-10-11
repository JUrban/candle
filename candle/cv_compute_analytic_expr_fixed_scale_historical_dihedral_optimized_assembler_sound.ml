(* ========================================================================== *)
(* Historical low-work dihedral: assemble the proved second-order result.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_assembler_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound;;

(* Shape is structural: the historical instruction always emits six gradient
   entries and six rows of six Hessian entries, independently of its data. *)

let candle_fs_hist_final_hessian_shape = prove
 (`!b delta_x4_value delta_x4_gradient delta_x4_hessian
      b_gradient b_hessian reciprocal_u result_gradient log_u_gradient.
     LENGTH
       (candle_fs_hist_final_hessian b delta_x4_value
         delta_x4_gradient delta_x4_hessian b_gradient b_hessian
         reciprocal_u result_gradient log_u_gradient) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_final_hessian b delta_x4_value
         delta_x4_gradient delta_x4_hessian b_gradient b_hessian
         reciprocal_u result_gradient log_u_gradient)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_final_hessian_def;
              candle_fs_hist_final_hessian_row_def; LENGTH; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_second_order_shape = prove
 (`!boxes root_delta_value root_four_x0.
     LENGTH
       (candle_fs_hist_second_gradient
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0)) = 6 /\
     LENGTH
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0)) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_order_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              candle_fs_hist_replace_three_def;
              LET_DEF; LET_END_DEF; FST; SND; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC candle_fs_hist_final_hessian_shape);;

(* This is the representation-independent assembler boundary.  The remaining
   production theorem must establish the three component enclosures from the
   source boxes and supplied roots; no per-entry theorem reconstruction is
   required after those vector/matrix facts are available. *)

let candle_fs_hist_second_order_reference_from_components = prove
 (`!boxes root_delta_value root_four_x0 values.
     candle_fs_interval_contains
       (candle_fs_hist_second_value
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values)) /\
     ALL2 candle_fs_interval_contains
       (candle_fs_hist_second_gradient
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6) /\
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i) 6) 6)
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_order
           boxes root_delta_value root_four_x0))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_second_components_from_data THEN
  MP_TAC
   (SPECL
     [`boxes:((num#num)#(num#num))list`;
      `root_delta_value:((num#num)#(num#num))`;
      `root_four_x0:((num#num)#(num#num))`]
     candle_fs_hist_second_order_shape) THEN
  ASM_REWRITE_TAC[]);;

end;;
