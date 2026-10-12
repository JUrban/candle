(* ========================================================================== *)
(* Case-10173 historical splice: analytic invariant of the logical item.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_logical_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_invariant.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_logical_sound;;

(* The private instruction carries the fixed result and its exact rational
   view.  Therefore the established result invariant is also precisely the
   invariant of the tagged logical stack item used by the surrounding source
   program. *)

let candle_case10173_hist_logical_item_analytic_invariant = prove
 (`!center_e box_e center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0 (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_case10173_hist_result center_boxes boxes radii
           center_root_delta center_root_four_x0
           box_root_delta box_root_four_x0))
       center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_case10173_hist_logical_item center_boxes boxes radii
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0)
       center_e box_e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_case10173_hist_logical_item_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def;
              LET_DEF; LET_END_DEF]);;

(* Specialize the universal historical-dihedral bridge at the exact logical
   item pushed by instruction 9. *)

let candle_case10173_hist_logical_item_source_analytic_invariant = prove
 (`!boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud
      (type_witness:real^6).
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)
       (candle_case10173_hist_source_dihedral_expr
         center_lp center_ln center_ld center_up center_un center_ud) /\
     (!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. p$(k + 1)) 6)
              (candle_case10173_hist_source_dihedral_expr
                box_lp box_ln box_ld box_up box_un box_ud)) /\
     candle_q_dim_jet_shape 6
       (candle_fs_first_to_q
         (candle_fs_hist_first_order_direct
           (candle_fs_interval_list_of_q
             (candle_q_center_environment_list boxes))
           center_root_delta center_root_four_x0)
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_order
             (candle_fs_interval_list_of_q boxes)
             box_root_delta box_root_four_x0))) /\
     &0 < candle_fs_hist_delta_real
       (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) /\
     &0 < candle_fs_hist_four_x0_real
       (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) /\
     candle_q_dim_jet_contains_components 6
       (candle_fs_first_to_q
         (candle_fs_hist_first_order_direct
           (candle_fs_interval_list_of_q
             (candle_q_center_environment_list boxes))
           center_root_delta center_root_four_x0)
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_order
             (candle_fs_interval_list_of_q boxes)
             box_root_delta box_root_four_x0)))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))) /\
     (!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> ALL2 (ALL2 candle_fs_interval_contains)
              (candle_fs_hist_second_hessian
                (candle_fs_hist_second_order
                  (candle_fs_interval_list_of_q boxes)
                  box_root_delta box_root_four_x0))
              (list_of_seq
                (\di. list_of_seq
                  (\dj. partial2 (dj + 1) (di + 1)
                    (candle_analytic_denote_dim
                      (candle_case10173_hist_source_dihedral_expr
                        box_lp box_ln box_ld box_up box_un box_ud)) p) 6) 6))
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_case10173_hist_logical_item
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0)
       (candle_case10173_hist_source_dihedral_expr
         center_lp center_ln center_ld center_up center_un center_ud)
       (candle_case10173_hist_source_dihedral_expr
         box_lp box_ln box_ld box_up box_un box_ud)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_case10173_hist_logical_item_analytic_invariant THEN
  MATCH_MP_TAC candle_case10173_hist_result_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

end;;
