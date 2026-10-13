(* ========================================================================== *)
(* Case-10173 historical splice: ordinary-context analytic handoff.          *)
(*                                                                            *)
(* The private fixed-scale instruction replaces only the authenticated       *)
(* dihedral segment.  This theorem carries its proved analytic invariant     *)
(* through the unchanged prefix/suffix program and identifies the executable *)
(* result with the resulting logical Taylor item.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_context_invariant = struct

open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_logical_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_invariant;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;
open Candle_cv_whole_box_dim_taylor;;

let candle_case10173_hist_checked_context_program_invariant = prove
 (`!context center_factor box_factor center_program box_program boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     candle_case10173_hist_context_valid 6 context /\
     candle_analytic_valid_dim 6 box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context center_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix context box_factor)
     ==>
     ?result.
       candle_cv_case10173_hist_program center_program box_program
         (candle_cv_q_interval_list boxes)
         (candle_cv_fs_interval_list
           [center_root_delta;center_root_four_x0;
            box_root_delta;box_root_four_x0]) =
       candle_cv_q_dim_taylor_model_result_encode
         (candle_fsa_logical_item_q_view result) /\
       candle_fsa_logical_item_analytic_invariant (vec 0:real^6) boxes
         result
         (candle_case10173_hist_context_center_expr context
           (candle_case10173_hist_source_dihedral_expr
             center_lp center_ln center_ld center_up center_un center_ud)
           center_factor)
         (candle_case10173_hist_context_box_expr context
           (candle_case10173_hist_source_dihedral_expr
             box_lp box_ln box_ld box_up box_un box_ud)
           box_factor)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `custom =
      candle_case10173_hist_logical_item
        (candle_q_center_environment_list boxes) boxes
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        center_root_delta center_root_four_x0
        box_root_delta box_root_four_x0` THEN
  SUBGOAL_THEN
   `candle_fsa_logical_item_analytic_invariant (vec 0:real^6) boxes
      custom
      (candle_case10173_hist_source_dihedral_expr
        center_lp center_ln center_ld center_up center_un center_ud)
      (candle_case10173_hist_source_dihedral_expr
        box_lp box_ln box_ld box_up box_un box_ud)`
   (LABEL_TAC "custom_invariant") THENL
   [EXPAND_TAC "custom" THEN
    MATCH_MP_TAC
      candle_case10173_hist_checked_logical_item_source_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (ISPECL
      [`context:(candle_analytic_expr#candle_analytic_expr)list`;
       `candle_case10173_hist_source_dihedral_expr
          center_lp center_ln center_ld center_up center_un center_ud`;
       `candle_case10173_hist_source_dihedral_expr
          box_lp box_ln box_ld box_up box_un box_ud`;
       `center_factor:candle_analytic_expr`;
       `box_factor:candle_analytic_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `[]:candle_fsa_logical_item_type list`;
       `custom:candle_fsa_logical_item_type`;
       `(vec 0:real^6)`]
      candle_case10173_hist_context_run_analytic_invariant) THEN
  ASM_REWRITE_TAC
    [candle_case10173_hist_dim_six;
     candle_case10173_hist_source_dihedral_valid;
     candle_case10173_hist_source_dihedral_erasure] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `result:candle_fsa_logical_item_type`
      STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `result:candle_fsa_logical_item_type` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_program_def;
     candle_cv_q_center_environment_list_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     LET_DEF;LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `candle_cv_case10173_hist_program_run
      (candle_cv_q_interval_list
        (candle_q_center_environment_list boxes))
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_list
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
      (candle_cv_fs_interval_list
        [center_root_delta;center_root_four_x0;
         box_root_delta;box_root_four_x0])
      (candle_cv_case10173_hist_program_of
        (candle_case10173_hist_context_center_prefix context)
        (candle_case10173_hist_context_center_suffix
          context center_factor))
      (candle_cv_case10173_hist_program_of
        (candle_case10173_hist_context_box_prefix context)
        (candle_case10173_hist_context_box_suffix context box_factor))
      (Cexp_num 0) =
    candle_cv_fsa_logical_stack_encode
      (candle_fsn_logical_program_run
        (candle_q_center_environment_list boxes) boxes
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_case10173_hist_context_center_suffix
          context center_factor)
        (candle_case10173_hist_context_box_suffix context box_factor)
        (CONS custom
          (candle_fsn_logical_program_run
            (candle_q_center_environment_list boxes) boxes
            (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
            (candle_case10173_hist_context_center_prefix context)
            (candle_case10173_hist_context_box_prefix context) [])))`
  SUBST1_TAC THENL
   [EXPAND_TAC "custom" THEN
    REWRITE_TAC[GSYM candle_cv_fsa_logical_stack_encode_def] THEN
    MATCH_MP_TAC candle_cv_case10173_hist_program_of_correct THEN
    MATCH_MP_TAC
      (SPECL
        [`context:(candle_analytic_expr#candle_analytic_expr)list`; `6`]
        candle_case10173_hist_context_prefix_length) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC
      [candle_cv_fsa_logical_item_head_correct;
       candle_cv_fsa_logical_item_to_q_correct;
       candle_fsa_logical_item_head_def]]);;

end;;
