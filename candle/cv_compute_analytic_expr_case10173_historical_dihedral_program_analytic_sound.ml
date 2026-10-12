(* ========================================================================== *)
(* Case-10173 historical splice: analytic invariant of the logical item.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_logical_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound;;
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

(* A right-associated additive source context is represented by a list of
   corresponding center/box left operands.  The private historical item fills
   the deepest hole; [factor] is its ordinary right multiplier.  These small
   definitions describe exactly the shape of the genuine case-10173 source,
   while keeping the composition proof independent of its thirteen operands. *)

let candle_case10173_hist_context_valid_def = define
 `(candle_case10173_hist_context_valid n [] <=> T) /\
  (candle_case10173_hist_context_valid n (CONS h t) <=>
     candle_analytic_valid_dim n (SND h) /\
     candle_analytic_erase_sqrt_certificates (FST h) =
       candle_analytic_erase_sqrt_certificates (SND h) /\
     candle_case10173_hist_context_valid n t)`;;

let candle_case10173_hist_context_center_prefix_def = define
 `(candle_case10173_hist_context_center_prefix [] = []) /\
  (candle_case10173_hist_context_center_prefix (CONS h t) =
     APPEND (candle_analytic_compile (FST h))
       (candle_case10173_hist_context_center_prefix t))`;;

let candle_case10173_hist_context_box_prefix_def = define
 `(candle_case10173_hist_context_box_prefix [] = []) /\
  (candle_case10173_hist_context_box_prefix (CONS h t) =
     APPEND (candle_analytic_compile (SND h))
       (candle_case10173_hist_context_box_prefix t))`;;

let candle_case10173_hist_context_center_suffix_def = define
 `(candle_case10173_hist_context_center_suffix [] factor =
     APPEND (candle_analytic_compile factor)
       [Candle_analytic_program_mul]) /\
  (candle_case10173_hist_context_center_suffix (CONS h t) factor =
     APPEND (candle_case10173_hist_context_center_suffix t factor)
       [Candle_analytic_program_add])`;;

let candle_case10173_hist_context_box_suffix_def = define
 `(candle_case10173_hist_context_box_suffix [] factor =
     APPEND (candle_analytic_compile factor)
       [Candle_analytic_program_mul]) /\
  (candle_case10173_hist_context_box_suffix (CONS h t) factor =
     APPEND (candle_case10173_hist_context_box_suffix t factor)
       [Candle_analytic_program_add])`;;

let candle_case10173_hist_context_center_expr_def = define
 `(candle_case10173_hist_context_center_expr [] hole factor =
     Candle_analytic_mul hole factor) /\
  (candle_case10173_hist_context_center_expr (CONS h t) hole factor =
     Candle_analytic_add (FST h)
       (candle_case10173_hist_context_center_expr t hole factor))`;;

let candle_case10173_hist_context_box_expr_def = define
 `(candle_case10173_hist_context_box_expr [] hole factor =
     Candle_analytic_mul hole factor) /\
  (candle_case10173_hist_context_box_expr (CONS h t) hole factor =
     Candle_analytic_add (SND h)
       (candle_case10173_hist_context_box_expr t hole factor))`;;

let candle_case10173_hist_context_prefix_length = prove
 (`!context n.
     candle_case10173_hist_context_valid n context
     ==>
     LENGTH (candle_case10173_hist_context_center_prefix context) =
     LENGTH (candle_case10173_hist_context_box_prefix context)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[candle_case10173_hist_context_valid_def;
                  candle_case10173_hist_context_center_prefix_def;
                  candle_case10173_hist_context_box_prefix_def;
                  LENGTH_APPEND] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent]);;

let candle_case10173_hist_context_suffix_length = prove
 (`!context n center_factor box_factor.
     candle_case10173_hist_context_valid n context /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor
     ==>
     LENGTH
       (candle_case10173_hist_context_center_suffix context center_factor) =
     LENGTH
       (candle_case10173_hist_context_box_suffix context box_factor)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[candle_case10173_hist_context_valid_def;
                  candle_case10173_hist_context_center_suffix_def;
                  candle_case10173_hist_context_box_suffix_def;
                  LENGTH; LENGTH_APPEND] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent]);;

let candle_case10173_hist_context_expression_well_formed = prove
 (`!context n center_hole box_hole center_factor box_factor.
     candle_case10173_hist_context_valid n context /\
     candle_analytic_valid_dim n box_hole /\
     candle_analytic_erase_sqrt_certificates center_hole =
       candle_analytic_erase_sqrt_certificates box_hole /\
     candle_analytic_valid_dim n box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor
     ==>
     candle_analytic_valid_dim n
       (candle_case10173_hist_context_box_expr
         context box_hole box_factor) /\
     candle_analytic_erase_sqrt_certificates
       (candle_case10173_hist_context_center_expr
         context center_hole center_factor) =
     candle_analytic_erase_sqrt_certificates
       (candle_case10173_hist_context_box_expr
         context box_hole box_factor)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_case10173_hist_context_valid_def;
                candle_case10173_hist_context_center_expr_def;
                candle_case10173_hist_context_box_expr_def;
                candle_analytic_valid_dim_def;
                candle_analytic_erase_sqrt_certificates_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_case10173_hist_context_valid_def] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `candle_analytic_valid_dim n
        (candle_case10173_hist_context_box_expr t box_hole box_factor) /\
      candle_analytic_erase_sqrt_certificates
        (candle_case10173_hist_context_center_expr
          t center_hole center_factor) =
      candle_analytic_erase_sqrt_certificates
        (candle_case10173_hist_context_box_expr
          t box_hole box_factor)`
     STRIP_ASSUME_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[candle_case10173_hist_context_center_expr_def;
                      candle_case10173_hist_context_box_expr_def;
                      candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]]]);;

(* Run the unchanged ordinary context around one authenticated private item.
   This is the reusable source-level handoff: all surrounding operands retain
   the standard compiler proof, and only the deepest dihedral subtree uses the
   specialized numerical implementation. *)

let candle_case10173_hist_context_run_analytic_invariant = prove
 (`!context center_hole box_hole center_factor box_factor boxes stack custom
      (type_witness:real^N).
     candle_case10173_hist_context_valid (dimindex (:N)) context /\
     candle_analytic_valid_dim (dimindex (:N)) box_hole /\
     candle_analytic_erase_sqrt_certificates center_hole =
       candle_analytic_erase_sqrt_certificates box_hole /\
     candle_analytic_valid_dim (dimindex (:N)) box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes custom center_hole box_hole
     ==>
     ?result.
       candle_fsn_logical_program_run
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
             (candle_case10173_hist_context_box_prefix context) stack)) =
       CONS result stack /\
       candle_fsa_logical_item_analytic_invariant type_witness boxes result
         (candle_case10173_hist_context_center_expr
           context center_hole center_factor)
         (candle_case10173_hist_context_box_expr
           context box_hole box_factor)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_case10173_hist_context_valid_def] THEN
    STRIP_TAC THEN
    MP_TAC
      (ISPECL
        [`box_factor:candle_analytic_expr`;
         `center_factor:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `CONS custom stack:candle_fsa_logical_item_type list`;
         `type_witness:real^N`]
        candle_fsn_logical_compile_run_analytic_invariant) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `factor_item:candle_fsa_logical_item_type`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
      `candle_fso_logical_item_mul
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        custom factor_item` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_case10173_hist_context_center_prefix_def;
                  candle_case10173_hist_context_box_prefix_def;
                  candle_case10173_hist_context_center_suffix_def;
                  candle_case10173_hist_context_box_suffix_def] THEN
      SUBGOAL_THEN
       `candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          [] [] stack = stack`
      SUBST1_TAC THENL
       [REWRITE_TAC[candle_fsn_logical_program_run_def]; ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          [Candle_analytic_program_mul]
          [Candle_analytic_program_mul]
          (candle_fsn_logical_program_run
            (candle_q_center_environment_list boxes) boxes
            (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
            (candle_analytic_compile center_factor)
            (candle_analytic_compile box_factor) (CONS custom stack))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
        ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
        ASM_REWRITE_TAC[candle_fsn_logical_program_run_def;
                        candle_fsn_logical_program_step_mul]];
      REWRITE_TAC[candle_case10173_hist_context_center_expr_def;
                  candle_case10173_hist_context_box_expr_def] THEN
      MATCH_MP_TAC candle_fso_logical_item_mul_analytic_invariant THEN
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_case10173_hist_context_valid_def] THEN
    STRIP_TAC THEN
    MP_TAC
      (ISPECL
        [`SND (h:candle_analytic_expr#candle_analytic_expr)`;
         `FST (h:candle_analytic_expr#candle_analytic_expr)`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `stack:candle_fsa_logical_item_type list`;
         `type_witness:real^N`]
        candle_fsn_logical_compile_run_analytic_invariant) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `left:candle_fsa_logical_item_type`
        STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM
      (MP_TAC o SPECL
        [`center_hole:candle_analytic_expr`;
         `box_hole:candle_analytic_expr`;
         `center_factor:candle_analytic_expr`;
         `box_factor:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `CONS left stack:candle_fsa_logical_item_type list`;
         `custom:candle_fsa_logical_item_type`;
         `type_witness:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `right:candle_fsa_logical_item_type`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
      `candle_fsa_logical_item_add T
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        left right` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_case10173_hist_context_center_prefix_def;
                  candle_case10173_hist_context_box_prefix_def;
                  candle_case10173_hist_context_center_suffix_def;
                  candle_case10173_hist_context_box_suffix_def] THEN
      SUBGOAL_THEN
       `candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (APPEND (candle_analytic_compile (FST h))
            (candle_case10173_hist_context_center_prefix t))
          (APPEND (candle_analytic_compile (SND h))
            (candle_case10173_hist_context_box_prefix t)) stack =
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_case10173_hist_context_center_prefix t)
          (candle_case10173_hist_context_box_prefix t) (CONS left stack)`
       SUBST1_TAC THENL
       [TRANS_TAC EQ_TRANS
         `candle_fsn_logical_program_run
            (candle_q_center_environment_list boxes) boxes
            (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
            (candle_case10173_hist_context_center_prefix t)
            (candle_case10173_hist_context_box_prefix t)
            (candle_fsn_logical_program_run
              (candle_q_center_environment_list boxes) boxes
              (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
              (candle_analytic_compile (FST h))
              (candle_analytic_compile (SND h)) stack)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
          ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          [Candle_analytic_program_add]
          [Candle_analytic_program_add]
          (candle_fsn_logical_program_run
            (candle_q_center_environment_list boxes) boxes
            (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
            (candle_case10173_hist_context_center_suffix t center_factor)
            (candle_case10173_hist_context_box_suffix t box_factor)
            (CONS custom
              (candle_fsn_logical_program_run
                (candle_q_center_environment_list boxes) boxes
                (candle_q_fixed_list_round_upper
                  (candle_q_radius_list boxes))
                (candle_case10173_hist_context_center_prefix t)
                (candle_case10173_hist_context_box_prefix t)
                (CONS left stack))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
        MATCH_MP_TAC
          (ISPECL
            [`t:(candle_analytic_expr#candle_analytic_expr)list`;
             `dimindex (:N)`;
             `center_factor:candle_analytic_expr`;
             `box_factor:candle_analytic_expr`]
            candle_case10173_hist_context_suffix_length) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[candle_fsn_logical_program_run_def;
                        candle_fsn_logical_program_step_add]];
      REWRITE_TAC[candle_case10173_hist_context_center_expr_def;
                  candle_case10173_hist_context_box_expr_def] THEN
      MP_TAC
        (ISPECL
          [`t:(candle_analytic_expr#candle_analytic_expr)list`;
           `dimindex (:N)`;
           `center_hole:candle_analytic_expr`;
           `box_hole:candle_analytic_expr`;
           `center_factor:candle_analytic_expr`;
           `box_factor:candle_analytic_expr`]
          candle_case10173_hist_context_expression_well_formed) THEN
      ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC candle_fsa_logical_item_add_analytic_invariant THEN
      ASM_REWRITE_TAC[]]]);;

end;;
