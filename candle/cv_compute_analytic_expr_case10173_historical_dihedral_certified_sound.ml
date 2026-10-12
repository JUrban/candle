(* ========================================================================== *)
(* Case-10173 historical splice: certified result and analytic soundness.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_invariant.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_certified_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_sound;;

let candle_case10173_hist_q_result_def = new_definition
 `candle_case10173_hist_q_result boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0 =
    candle_fs_result_to_q
      (candle_case10173_hist_result
        (candle_q_center_environment_list boxes) boxes
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        center_root_delta center_root_four_x0
        box_root_delta box_root_four_x0)`;;

let candle_cv_case10173_hist_program_q_result_correct = prove
 (`!center_program box_program center_prefix box_prefix boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     LENGTH center_prefix = LENGTH box_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_final_program center_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_final_program box_prefix
     ==>
     candle_cv_case10173_hist_program center_program box_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_case10173_hist_q_result boxes
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0)`,
  REWRITE_TAC[candle_case10173_hist_q_result_def] THEN
  MATCH_ACCEPT_TAC candle_cv_case10173_hist_program_correct);;

let candle_cv_case10173_hist_finish_q_result_correct = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_q_dim_taylor_model_certified_finish
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_taylor_model_result_encode
         (candle_case10173_hist_q_result boxes
           center_root_delta center_root_four_x0
           box_root_delta box_root_four_x0)) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_taylor_model_result_domain
               (candle_case10173_hist_q_result boxes
                 center_root_delta center_root_four_x0
                 box_root_delta box_root_four_x0) /\
             candle_q_box_valid_list boxes /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_model_certified_upper
                  (candle_case10173_hist_q_result boxes
                    center_root_delta center_root_four_x0
                    box_root_delta box_root_four_x0)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_model_certified_upper
           (candle_case10173_hist_q_result boxes
             center_root_delta center_root_four_x0
             box_root_delta box_root_four_x0)))`,
  MATCH_ACCEPT_TAC candle_cv_q_dim_taylor_model_certified_finish_correct);;

let candle_cv_case10173_hist_certified_check_correct = prove
 (`!center_program box_program center_prefix box_prefix boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     LENGTH center_prefix = LENGTH box_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_final_program center_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_final_program box_prefix
     ==>
     candle_cv_case10173_hist_certified_check
       center_program box_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_taylor_model_result_domain
               (candle_case10173_hist_q_result boxes
                 center_root_delta center_root_four_x0
                 box_root_delta box_root_four_x0) /\
             candle_q_box_valid_list boxes /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_model_certified_upper
                  (candle_case10173_hist_q_result boxes
                    center_root_delta center_root_four_x0
                    box_root_delta box_root_four_x0)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_model_certified_upper
           (candle_case10173_hist_q_result boxes
             center_root_delta center_root_four_x0
             box_root_delta box_root_four_x0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_cv_q_dim_taylor_model_certified_finish
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_dim_taylor_model_result_encode
        (candle_case10173_hist_q_result boxes
          center_root_delta center_root_four_x0
          box_root_delta box_root_four_x0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_cv_case10173_hist_certified_check_def] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC
      (SPECL
        [`center_program:cval`; `box_program:cval`;
         `center_prefix:candle_analytic_instruction list`;
         `box_prefix:candle_analytic_instruction list`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_root_delta:(num#num)#(num#num)`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `box_root_delta:(num#num)#(num#num)`;
         `box_root_four_x0:(num#num)#(num#num)`]
        candle_cv_case10173_hist_program_q_result_correct) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC candle_cv_case10173_hist_finish_q_result_correct]);;

(* This factors the final analytic argument away from any particular program:
   a result carrying the universal invariant bounds the source expression by
   its cached outward-rounded upper endpoint throughout the box. *)

let candle_q_dim_taylor_model_invariant_upper_sound = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e /\
     candle_q_dim_taylor_model_result_domain result
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim box_e p <=
       candle_q_real
         (candle_q_dim_taylor_model_certified_upper result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ASSUME
      `candle_q_dim_taylor_model_result_analytic_invariant
        (type_witness:real^N) boxes result center_e box_e`) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let contains_all =
    ASSUME
     `!(p:real^N). p IN interval
        [candle_q_box_lower_vector boxes,
         candle_q_box_upper_vector boxes]
        ==> candle_q_dim_analytic_contains (dimindex (:N))
              (candle_q_dim_taylor_model_proxy
                (result:
                  bool#
                  ((((num#num)#num)#(num#num)#num)#
                   (((num#num)#num)#(num#num)#num)list#
                   ((((num#num)#num)#(num#num)#num)list)list)#
                  (((num#num)#num)#(num#num)#num)#
                  (((num#num)#num)#(num#num)#num)list#
                  ((((num#num)#num)#(num#num)#num)list)list))
              (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e` in
  let contains_at_p =
    MATCH_MP (SPEC `p:real^N` contains_all)
      (ASSUME
       `(p:real^N) IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`) in
  let value_contains =
    CONJUNCT1
      (REWRITE_RULE
        [candle_q_dim_analytic_contains_def;
         candle_q_dim_jet_contains_components_def]
        contains_at_p) in
  let upper_bound =
    CONJUNCT2
      (REWRITE_RULE [candle_q_interval_contains_def] value_contains) in
  MP_TAC upper_bound THEN
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
              candle_q_dim_taylor_model_certified_upper_def;
              candle_analytic_denote_dim_def; FST; SND] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let candle_q_dim_taylor_model_invariant_accept_sound = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e /\
     candle_q_dim_taylor_model_result_domain result /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper result))
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  MP_TAC
    (MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `result:
            bool#
            ((((num#num)#num)#(num#num)#num)#
             (((num#num)#num)#(num#num)#num)list#
             ((((num#num)#num)#(num#num)#num)list)list)#
            (((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list`;
         `type_witness:real^N`]
        candle_q_dim_taylor_model_invariant_upper_sound)
      (CONJ
        (ASSUME
          `candle_q_dim_taylor_model_result_analytic_invariant
            (type_witness:real^N) boxes result center_e box_e`)
        (ASSUME
          `candle_q_dim_taylor_model_result_domain
            (result:
              bool#
              ((((num#num)#num)#(num#num)#num)#
               (((num#num)#num)#(num#num)#num)list#
               ((((num#num)#num)#(num#num)#num)list)list)#
              (((num#num)#num)#(num#num)#num)#
              (((num#num)#num)#(num#num)#num)list#
              ((((num#num)#num)#(num#num)#num)list)list)`))) THEN
  DISCH_THEN (fun th -> MP_TAC (MATCH_MP (SPEC `p:real^N` th)
    (ASSUME
      `(p:real^N) IN interval
        [candle_q_box_lower_vector boxes,
         candle_q_box_upper_vector boxes]`))) THEN
  MP_TAC
    (REWRITE_RULE
      [candle_q_le_real; candle_q_dim_real_zero; REAL_NOT_LE]
      (ASSUME
        `~(candle_q_le candle_q_zero
            (candle_q_dim_taylor_model_certified_upper
              (result:
                bool#
                ((((num#num)#num)#(num#num)#num)#
                 (((num#num)#num)#(num#num)#num)list#
                 ((((num#num)#num)#(num#num)#num)list)list)#
                (((num#num)#num)#(num#num)#num)#
                (((num#num)#num)#(num#num)#num)list#
                ((((num#num)#num)#(num#num)#num)list)list)))`)) THEN
  REAL_ARITH_TAC);;

end;;
