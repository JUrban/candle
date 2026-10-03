(* ========================================================================== *)
(* Certified soundness of the fixed nonlinear analytic Taylor program.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;

let candle_q_dim_taylor_model_program_fixed_nonlinear_def = new_definition
 `candle_q_dim_taylor_model_program_fixed_nonlinear
      center_program box_program boxes =
    let item =
      candle_fsa_logical_item_head
        (candle_q_center_environment_list boxes) boxes
        (candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          center_program box_program []) in
    candle_fsa_logical_item_q_view item`;;

let candle_cv_fsn_program_correct = prove
 (`!center_program box_program boxes.
     candle_cv_fsn_program
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_program_fixed_nonlinear
         center_program box_program boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_program_def;
              candle_q_dim_taylor_model_program_fixed_nonlinear_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_fixed_list_round_upper_correct;
              GSYM candle_cv_fsa_logical_stack_encode_def;
              candle_cv_fsn_logical_program_run_correct;
              candle_cv_fsa_logical_item_head_correct;
              candle_cv_fsa_logical_item_to_q_correct;
              LET_DEF; LET_END_DEF]);;

let candle_q_dim_taylor_model_program_fixed_nonlinear_result = prove
 (`!center_program box_program boxes result.
     candle_fsn_logical_program_run
       (candle_q_center_environment_list boxes) boxes
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       center_program box_program [] = CONS result []
     ==>
     candle_q_dim_taylor_model_program_fixed_nonlinear
       center_program box_program boxes =
     candle_fsa_logical_item_q_view result`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_nonlinear_def;
                  candle_fsa_logical_item_head_def;
                  LET_DEF; LET_END_DEF]);;

let candle_q_dim_taylor_model_fixed_nonlinear_compile_analytic_invariant = prove
 (`!center_e box_e boxes (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_program_fixed_nonlinear
         (candle_analytic_compile center_e)
         (candle_analytic_compile box_e) boxes)
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`box_e:candle_analytic_expr`; `center_e:candle_analytic_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `[]:candle_fsa_logical_item_type list`; `type_witness:real^N`]
      candle_fsn_logical_compile_run_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `result:candle_fsa_logical_item_type`
      (CONJUNCTS_THEN2 (LABEL_TAC "run")
        (LABEL_TAC "item_invariant"))) THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_program_fixed_nonlinear
      (candle_analytic_compile center_e)
      (candle_analytic_compile box_e) boxes =
    candle_fsa_logical_item_q_view result`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_nonlinear_result THEN
    USE_THEN "run" ACCEPT_TAC;
    MATCH_MP_TAC candle_fsa_logical_item_q_view_analytic_invariant THEN
    USE_THEN "item_invariant" ACCEPT_TAC]);;

let candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_def =
  new_definition
 `candle_q_dim_taylor_model_fixed_nonlinear_certified_accept
      center_e box_e boxes <=>
    candle_q_dim_taylor_model_result_domain
      (candle_q_dim_taylor_model_program_fixed_nonlinear
        (candle_analytic_compile center_e)
        (candle_analytic_compile box_e) boxes) /\
    candle_q_box_valid_list boxes /\
    candle_analytic_erase_sqrt_certificates center_e =
      candle_analytic_erase_sqrt_certificates box_e /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_taylor_model_certified_upper
         (candle_q_dim_taylor_model_program_fixed_nonlinear
           (candle_analytic_compile center_e)
           (candle_analytic_compile box_e) boxes)))`;;

let candle_cv_fsn_certified_check_correct = prove
 (`!center_e box_e boxes.
     candle_cv_fsn_certified_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_taylor_model_result_domain
               (candle_q_dim_taylor_model_program_fixed_nonlinear
                 (candle_analytic_compile center_e)
                 (candle_analytic_compile box_e) boxes) /\
             candle_q_box_valid_list boxes /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_model_certified_upper
                  (candle_q_dim_taylor_model_program_fixed_nonlinear
                    (candle_analytic_compile center_e)
                    (candle_analytic_compile box_e) boxes)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_model_certified_upper
           (candle_q_dim_taylor_model_program_fixed_nonlinear
             (candle_analytic_compile center_e)
             (candle_analytic_compile box_e) boxes)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_certified_check_def;
              candle_cv_fsn_program_correct;
              candle_cv_q_dim_taylor_model_certified_finish_correct]);;

let candle_q_dim_taylor_model_fixed_nonlinear_certified_upper_sound = prove
 (`!center_e box_e boxes (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_nonlinear
         (candle_analytic_compile center_e)
         (candle_analytic_compile box_e) boxes)
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim box_e p <=
       candle_q_real
         (candle_q_dim_taylor_model_certified_upper
           (candle_q_dim_taylor_model_program_fixed_nonlinear
             (candle_analytic_compile center_e)
             (candle_analytic_compile box_e) boxes))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes
      (candle_q_dim_taylor_model_program_fixed_nonlinear
        (candle_analytic_compile center_e)
        (candle_analytic_compile box_e) boxes)
      center_e box_e`
   (LABEL_TAC "invariant") THENL
   [MATCH_MP_TAC
      candle_q_dim_taylor_model_fixed_nonlinear_compile_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N))
      (candle_q_dim_taylor_model_proxy
        (candle_q_dim_taylor_model_program_fixed_nonlinear
          (candle_analytic_compile center_e)
          (candle_analytic_compile box_e) boxes))
      (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) box_e`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
              candle_q_interval_contains_def;
              candle_q_dim_taylor_model_certified_upper_def;
              candle_analytic_denote_dim_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_sound = prove
 (`!center_e box_e boxes.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_taylor_model_fixed_nonlinear_certified_accept
       center_e box_e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_def] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `ARB:real^N`]
        candle_q_dim_taylor_model_fixed_nonlinear_certified_upper_sound)
      (end_itlist CONJ
        [ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_e`;
         ASSUME
          `candle_analytic_erase_sqrt_certificates center_e =
           candle_analytic_erase_sqrt_certificates box_e`;
         ASSUME
          `LENGTH
             (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`;
         ASSUME `candle_q_box_valid_list boxes`;
         ASSUME
          `candle_q_dim_taylor_model_result_domain
            (candle_q_dim_taylor_model_program_fixed_nonlinear
              (candle_analytic_compile center_e)
              (candle_analytic_compile box_e) boxes)`]) in
  let upper_at_p =
    MATCH_MP (SPEC `p:real^N` upper_th)
      (ASSUME
        `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`) in
  let upper_negative =
    REWRITE_RULE[candle_q_le_real; candle_q_dim_real_zero; REAL_NOT_LE]
      (ASSUME
        `~(candle_q_le candle_q_zero
            (candle_q_dim_taylor_model_certified_upper
              (candle_q_dim_taylor_model_program_fixed_nonlinear
                (candle_analytic_compile center_e)
                (candle_analytic_compile box_e) boxes)))`) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim box_e (p:real^N)`;
         `candle_q_real
           (candle_q_dim_taylor_model_certified_upper
             (candle_q_dim_taylor_model_program_fixed_nonlinear
               (candle_analytic_compile center_e)
               (candle_analytic_compile box_e) boxes))`;
         `&0`]
        REAL_LET_TRANS)
      (CONJ upper_at_p upper_negative)));;

end;;
