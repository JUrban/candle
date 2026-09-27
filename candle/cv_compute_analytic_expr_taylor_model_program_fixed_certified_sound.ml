(* ========================================================================== *)
(* Certified soundness of the fixed-polynomial analytic Taylor program.       *)
(*                                                                            *)
(* Polynomial blocks use the proved fixed-scale evaluator; all other          *)
(* instructions retain the established rational Taylor semantics.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_representation.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_certified_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_representation;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;

let candle_q_dim_taylor_model_fixed_certified_accept_def = new_definition
 `candle_q_dim_taylor_model_fixed_certified_accept center_e box_e boxes <=>
    candle_q_dim_taylor_model_result_domain
      (candle_q_dim_taylor_model_program_fixed
        (candle_analytic_compile center_e)
        (candle_analytic_compile box_e) boxes) /\
    candle_q_box_valid_list boxes /\
    candle_analytic_erase_sqrt_certificates center_e =
      candle_analytic_erase_sqrt_certificates box_e /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_taylor_model_certified_upper
         (candle_q_dim_taylor_model_program_fixed
           (candle_analytic_compile center_e)
           (candle_analytic_compile box_e) boxes)))`;;

let candle_cv_fs_q_dim_taylor_model_certified_check_correct = prove
 (`!center_e box_e boxes.
     candle_cv_fs_q_dim_taylor_model_certified_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_taylor_model_result_domain
               (candle_q_dim_taylor_model_program_fixed
                 (candle_analytic_compile center_e)
                 (candle_analytic_compile box_e) boxes) /\
             candle_q_box_valid_list boxes /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_model_certified_upper
                  (candle_q_dim_taylor_model_program_fixed
                    (candle_analytic_compile center_e)
                    (candle_analytic_compile box_e) boxes)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_model_certified_upper
           (candle_q_dim_taylor_model_program_fixed
             (candle_analytic_compile center_e)
             (candle_analytic_compile box_e) boxes)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_q_dim_taylor_model_certified_check_def;
              candle_cv_fs_q_dim_taylor_model_program_correct;
              candle_cv_q_dim_taylor_model_certified_finish_correct]);;

let candle_q_dim_taylor_model_fixed_compile_analytic_invariant = prove
 (`!center_e box_e boxes (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_program_fixed
         (candle_analytic_compile center_e)
         (candle_analytic_compile box_e) boxes)
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`box_e:candle_analytic_expr`; `center_e:candle_analytic_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `[]:
          (bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)list`;
       `type_witness:real^N`]
      candle_q_dim_taylor_model_fixed_compile_run_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN
      `result:
         bool#
         ((((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)#
         (((num#num)#num)#(num#num)#num)#
         (((num#num)#num)#(num#num)#num)list#
         ((((num#num)#num)#(num#num)#num)list)list`
      STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_def;
                  candle_q_dim_taylor_model_result_head_def]);;

let candle_q_dim_taylor_model_fixed_certified_upper_sound = prove
 (`!center_e box_e boxes (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed
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
           (candle_q_dim_taylor_model_program_fixed
             (candle_analytic_compile center_e)
             (candle_analytic_compile box_e) boxes))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes
      (candle_q_dim_taylor_model_program_fixed
        (candle_analytic_compile center_e)
        (candle_analytic_compile box_e) boxes)
      center_e box_e`
   (LABEL_TAC "invariant") THENL
   [MATCH_MP_TAC candle_q_dim_taylor_model_fixed_compile_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_analytic_contains (dimindex (:N))
      (candle_q_dim_taylor_model_proxy
        (candle_q_dim_taylor_model_program_fixed
          (candle_analytic_compile center_e)
          (candle_analytic_compile box_e) boxes))
      (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) box_e`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (ASSUME
      `candle_q_dim_analytic_contains (dimindex (:N))
        (candle_q_dim_taylor_model_proxy
          (candle_q_dim_taylor_model_program_fixed
            (candle_analytic_compile center_e)
            (candle_analytic_compile box_e) boxes))
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) box_e`) THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
              candle_q_interval_contains_def;
              candle_q_dim_taylor_model_certified_upper_def;
              candle_analytic_denote_dim_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_certified_accept_sound = prove
 (`!center_e box_e boxes.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_taylor_model_fixed_certified_accept center_e box_e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_fixed_certified_accept_def] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `ARB:real^N`]
        candle_q_dim_taylor_model_fixed_certified_upper_sound)
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
            (candle_q_dim_taylor_model_program_fixed
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
              (candle_q_dim_taylor_model_program_fixed
                (candle_analytic_compile center_e)
                (candle_analytic_compile box_e) boxes)))`) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim box_e (p:real^N)`;
         `candle_q_real
           (candle_q_dim_taylor_model_certified_upper
             (candle_q_dim_taylor_model_program_fixed
               (candle_analytic_compile center_e)
               (candle_analytic_compile box_e) boxes))`;
         `&0`]
        REAL_LET_TRANS)
      (CONJ upper_at_p upper_negative)));;

end;;
