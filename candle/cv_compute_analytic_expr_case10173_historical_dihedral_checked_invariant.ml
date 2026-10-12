(* ========================================================================== *)
(* Case-10173 checked historical splice: complete per-cell source invariant.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_production_contract_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_checked_invariant = struct

open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_production_contract_sound;;

let candle_case10173_hist_root_lookup_four = prove
 (`!first second third fourth.
     candle_fs_interval_lookup 0 [first;second;third;fourth] = first /\
     candle_fs_interval_lookup 1 [first;second;third;fourth] = second /\
     candle_fs_interval_lookup 2 [first;second;third;fourth] = third /\
     candle_fs_interval_lookup 3 [first;second;third;fourth] = fourth`,
  REPEAT GEN_TAC THEN
  MP_TAC (ARITH_RULE `1 = SUC 0`) THEN
  MP_TAC (ARITH_RULE `2 = SUC (SUC 0)`) THEN
  MP_TAC (ARITH_RULE `3 = SUC (SUC (SUC 0))`) THEN
  REPEAT (DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_fs_interval_lookup_def]);;

(* A checked root record plus the production guard discharges every analytic
   premise used by the private low-work instruction.  This theorem is uniform
   in the source sqrt-certificate fields: they affect compilation data but not
   the source denotation. *)

let candle_case10173_hist_checked_source_contract = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0]
     ==>
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
                        box_lp box_ln box_ld box_up box_un box_ud)) p) 6) 6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`]
      candle_case10173_hist_root_record_valid_components) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP_TAC
    (ASSUME
      `candle_case10173_hist_production_guard boxes
        [center_root_delta;center_root_four_x0;
         box_root_delta;box_root_four_x0]`) THEN
  REWRITE_TAC[candle_case10173_hist_production_guard_def;
              candle_fs_interval_lookup_def;
              LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_case10173_hist_root_lookup_four]) THEN
  MP_TAC
    (SPECL
      [`boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`]
      candle_case10173_hist_root_record_semantics) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_positive_interval center_root_delta /\
    candle_fs_hist_positive_interval center_root_four_x0 /\
    candle_fs_hist_positive_interval box_root_delta /\
    candle_fs_hist_positive_interval box_root_four_x0`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC
      [candle_fs_hist_positive_root_certificate_root_interval];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_positive_interval
      (candle_fs_hist_second_value
        (candle_fs_hist_delta_second
          (candle_fs_interval_list_of_q boxes)))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC
      [candle_fs_hist_positive_root_certificate_input_interval];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_positive_interval
      (candle_fs_interval_lookup 0
        (candle_fs_interval_list_of_q boxes))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_scale_four_root_input_positive];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_interval_list_of_q
        (candle_q_center_environment_list boxes))
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)`
  (LABEL_TAC "center_environment_contains") THENL
   [MATCH_MP_TAC candle_case10173_fs_center_environment_contains_six THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_interval_list_of_q boxes)
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)`
  (LABEL_TAC "box_contains_center") THENL
   [MATCH_MP_TAC candle_case10173_fs_box_contains_center_six THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(candle_q_box_center_vector boxes : real^6) IN
      interval
        [candle_q_box_lower_vector boxes,
         candle_q_box_upper_vector boxes]`
  (LABEL_TAC "center_in_box") THENL
   [MATCH_MP_TAC candle_case10173_q_box_center_in_interval_six THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (MATCH_MP
      (SPEC `(candle_q_box_center_vector boxes : real^6)`
        (ASSUME
          `!(p:real^6). p IN interval
             [candle_q_box_lower_vector boxes,
              candle_q_box_upper_vector boxes]
           ==>
           &0 < candle_fs_hist_delta_real (\k. p$(k + 1)) /\
           &0 < candle_fs_hist_four_x0_real (\k. p$(k + 1)) /\
           candle_fs_interval_contains box_root_delta
             (sqrt (candle_fs_hist_delta_real (\k. p$(k + 1)))) /\
           candle_fs_interval_contains box_root_four_x0
             (sqrt (candle_fs_hist_four_x0_real (\k. p$(k + 1))))`))
      (ASSUME
        `(candle_q_box_center_vector boxes : real^6) IN
          interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_first_value
        (candle_fs_hist_first_order_direct
          (candle_fs_interval_list_of_q
            (candle_q_center_environment_list boxes))
          center_root_delta center_root_four_x0))
      (candle_hist_real_jet_value
        (candle_fs_hist_reference_dihedral_real_jet
          (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))) /\
    ALL2 candle_fs_interval_contains
      (candle_fs_first_gradient
        (candle_fs_hist_first_order_direct
          (candle_fs_interval_list_of_q
            (candle_q_center_environment_list boxes))
          center_root_delta center_root_four_x0))
      (list_of_seq
        (candle_hist_real_jet_gradient
          (candle_fs_hist_reference_dihedral_real_jet
            (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))) 6)`
  (fun theorem ->
    ASSUME_TAC (CONJUNCT1 theorem) THEN
    ASSUME_TAC (CONJUNCT2 theorem)) THENL
   [MATCH_MP_TAC candle_case10173_hist_first_order_reference_contains THEN
    ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length;
                    candle_q_center_environment_list_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fs_hist_second_hessian
        (candle_fs_hist_second_order
          (candle_fs_interval_list_of_q boxes)
          box_root_delta box_root_four_x0))
      (list_of_seq
        (\i. list_of_seq
          (candle_hist_real_jet_hessian
            (candle_fs_hist_reference_dihedral_real_jet
              (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))) i)
          6) 6)`
  (LABEL_TAC "center_hessian_contains") THENL
   [MATCH_MP_TAC
      candle_case10173_hist_second_order_reference_hessian_contains THEN
    ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
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
          (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))))`
  (LABEL_TAC "center_jet_contains") THENL
   [MATCH_MP_TAC candle_fs_first_components_from_data THEN
    ASM_REWRITE_TAC[candle_case10173_hist_result_jet_shape];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(p:real^6). p IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order
           (candle_fs_interval_list_of_q boxes)
           box_root_delta box_root_four_x0))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim
               (candle_case10173_hist_source_dihedral_expr
                 box_lp box_ln box_ld box_up box_un box_ud)) p) 6) 6)`
  (LABEL_TAC "box_hessian_contains_source") THENL
   [X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ALL2 candle_fs_interval_contains
        (candle_fs_interval_list_of_q boxes)
        (list_of_seq (\k. (p:real^6)$(k + 1)) 6)`
    (LABEL_TAC "point_contains") THENL
     [MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
      MATCH_MP_TAC candle_case10173_q_box_stack_contains_vector_six THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC
      (MATCH_MP
        (SPEC `p:real^6`
          (ASSUME
            `!(p:real^6). p IN interval
               [candle_q_box_lower_vector boxes,
                candle_q_box_upper_vector boxes]
             ==>
             &0 < candle_fs_hist_delta_real (\k. p$(k + 1)) /\
             &0 < candle_fs_hist_four_x0_real (\k. p$(k + 1)) /\
             candle_fs_interval_contains box_root_delta
               (sqrt (candle_fs_hist_delta_real (\k. p$(k + 1)))) /\
             candle_fs_interval_contains box_root_four_x0
               (sqrt (candle_fs_hist_four_x0_real (\k. p$(k + 1))))`))
        (ASSUME
          `(p:real^6) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `ALL2 (ALL2 candle_fs_interval_contains)
        (candle_fs_hist_second_hessian
          (candle_fs_hist_second_order
            (candle_fs_interval_list_of_q boxes)
            box_root_delta box_root_four_x0))
        (list_of_seq
          (\i. list_of_seq
            (candle_hist_real_jet_hessian
              (candle_fs_hist_reference_dihedral_real_jet
                (\k. (p:real^6)$(k + 1))) i) 6) 6)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
        candle_case10173_hist_second_order_reference_hessian_contains THEN
      ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length];
      ALL_TAC] THEN
    MP_TAC
      (SPECL
        [`(\k. (p:real^6)$(k + 1)):num->real`; `p:real^6`;
         `box_lp:num`; `box_ln:num`; `box_ld:num`;
         `box_up:num`; `box_un:num`; `box_ud:num`]
        candle_case10173_hist_reference_hessian_is_source) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_case10173_hist_source_dihedral_regular THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_case10173_hist_source_dihedral_regular THEN
    MP_TAC
      (MATCH_MP
        (SPEC `p:real^6`
          (ASSUME
            `!(p:real^6). p IN interval
               [candle_q_box_lower_vector boxes,
                candle_q_box_upper_vector boxes]
             ==>
             &0 < candle_fs_hist_delta_real (\k. p$(k + 1)) /\
             &0 < candle_fs_hist_four_x0_real (\k. p$(k + 1)) /\
             candle_fs_interval_contains box_root_delta
               (sqrt (candle_fs_hist_delta_real (\k. p$(k + 1)))) /\
             candle_fs_interval_contains box_root_four_x0
               (sqrt (candle_fs_hist_four_x0_real (\k. p$(k + 1))))`))
        (ASSUME
          `(p:real^6) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) THEN
    MESON_TAC[];
    MATCH_ACCEPT_TAC
      (SPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_root_delta:(num#num)#(num#num)`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `box_root_delta:(num#num)#(num#num)`;
         `box_root_four_x0:(num#num)#(num#num)`]
        candle_case10173_hist_result_jet_shape);
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "center_jet_contains" ACCEPT_TAC;
    USE_THEN "box_hessian_contains_source" ACCEPT_TAC]);;

let candle_case10173_hist_checked_logical_item_source_analytic_invariant = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0]
     ==>
     candle_fsa_logical_item_analytic_invariant (vec 0:real^6) boxes
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
  MATCH_MP_TAC candle_case10173_hist_logical_item_source_analytic_invariant THEN
  MP_TAC
    (SPECL
      [`boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`;
       `center_lp:num`; `center_ln:num`; `center_ld:num`;
       `center_up:num`; `center_un:num`; `center_ud:num`;
       `box_lp:num`; `box_ln:num`; `box_ld:num`;
       `box_up:num`; `box_un:num`; `box_ud:num`]
      candle_case10173_hist_checked_source_contract) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

end;;
