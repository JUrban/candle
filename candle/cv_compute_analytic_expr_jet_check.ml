(* ========================================================================== *)
(* Reflected whole-box Taylor checking for nested analytic shared jets.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A single compiled analytic source program is  *)
(* evaluated at the box center and over the whole box.  Values, gradients,   *)
(* Hessians, and domain guards remain data until one universal Taylor theorem *)
(* turns an accepted result into the source-level inequality.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_program_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_sound.ml";;

module Candle_cv_analytic_expr_jet_check = struct

open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_sound;;

let candle_q_dim_analytic_jet_whole_box_upper_def = new_definition
 `candle_q_dim_analytic_jet_whole_box_upper e boxes =
    candle_q_dim_jet_taylor_upper boxes
      (candle_q_dim_analytic_jet
        (candle_q_center_environment_list boxes) e)
      (candle_q_dim_analytic_jet boxes e)`;;

let candle_q_dim_analytic_jet_whole_box_numerical_accept_def = new_definition
 `candle_q_dim_analytic_jet_whole_box_numerical_accept e boxes <=>
    candle_q_box_valid_list boxes /\
    candle_q_dim_analytic_domain
      (candle_q_center_environment_list boxes) e /\
    candle_q_dim_analytic_domain boxes e /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_analytic_jet_whole_box_upper e boxes))`;;

let candle_cv_q_dim_analytic_jet_upper_pair_def = new_definition
 `candle_cv_q_dim_analytic_jet_upper_pair boxes center_result box_result =
    candle_cv_q_dim_taylor_upper
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_dim_jet_f
        (candle_cv_q_dim_analytic_result_jet center_result))
      (candle_cv_q_dim_jet_gradient
        (candle_cv_q_dim_analytic_result_jet center_result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_analytic_result_jet box_result))`;;

let candle_cv_q_dim_analytic_jet_finish_def = new_definition
 `candle_cv_q_dim_analytic_jet_finish boxes center_result box_result =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain center_result)
        (candle_cv_q_dim_analytic_result_domain box_result))
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_analytic_jet_upper_pair
        boxes center_result box_result)`;;

let candle_cv_q_dim_analytic_jet_whole_box_check_def = new_definition
 `candle_cv_q_dim_analytic_jet_whole_box_check program boxes =
    candle_cv_q_dim_analytic_jet_finish boxes
      (candle_cv_q_dim_analytic_program
        (candle_cv_q_center_environment_list boxes) program)
      (candle_cv_q_dim_analytic_program boxes program)`;;

let candle_cv_q_dim_analytic_jet_upper_pair_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_jet_upper_pair
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     candle_cv_q
       (candle_q_dim_jet_taylor_upper boxes
         (candle_q_dim_analytic_result_jet center_result)
         (candle_q_dim_analytic_result_jet box_result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_jet_upper_pair_def;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_upper_correct;
              candle_q_dim_jet_taylor_upper_def]);;

let candle_cv_q_dim_analytic_jet_finish_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_jet_finish
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     Cexp_pair
       (Cexp_num
         (if candle_q_box_valid_list boxes /\
             candle_q_dim_analytic_result_domain center_result /\
             candle_q_dim_analytic_result_domain box_result /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_jet_taylor_upper boxes
                  (candle_q_dim_analytic_result_jet center_result)
                  (candle_q_dim_analytic_result_jet box_result)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_jet_taylor_upper boxes
           (candle_q_dim_analytic_result_jet center_result)
           (candle_q_dim_analytic_result_jet box_result)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_jet_finish_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_bool_def;
              candle_cv_bool_and_def;
              candle_cv_q_box_valid_list_correct;
              candle_cv_q_dim_analytic_jet_upper_pair_correct;
              candle_cv_q_dim_whole_box_finish_def;
              candle_cv_q_zero_def; candle_cv_q_le_correct;
              cexp_if_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_analytic_jet_whole_box_check_correct = prove
 (`!e boxes.
     candle_cv_q_dim_analytic_jet_whole_box_check
       (candle_cv_analytic_instruction_list (candle_analytic_compile e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_analytic_jet_whole_box_numerical_accept e boxes
          then SUC 0 else 0))
       (candle_cv_q (candle_q_dim_analytic_jet_whole_box_upper e boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_jet_whole_box_check_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_dim_analytic_compile_program_correct;
              candle_cv_q_dim_analytic_jet_finish_correct;
              candle_q_dim_analytic_result_domain_def;
              candle_q_dim_analytic_result_jet_def;
              candle_q_dim_analytic_jet_whole_box_numerical_accept_def;
              candle_q_dim_analytic_jet_whole_box_upper_def]);;

let candle_cv_q_dim_analytic_jet_compute_eqs =
  union candle_cv_q_dim_analytic_program_compute_eqs
    candle_cv_q_dim_whole_box_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_analytic_jet_upper_pair_def;
    candle_cv_q_dim_analytic_jet_finish_def;
    candle_cv_q_dim_analytic_jet_whole_box_check_def];;

let candle_q_dim_analytic_jet_center_shape = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_analytic_jet
         (candle_q_center_environment_list boxes) e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ACCEPT_TAC
    (REWRITE_RULE
      [candle_q_center_environment_list_length;
       ASSUME
        `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`]
      (ISPECL
        [`e:candle_analytic_expr`;
         `candle_q_center_environment_list
           (boxes:(((num#num)#num)#((num#num)#num))list)`]
        candle_q_dim_analytic_jet_shape)));;

let candle_q_dim_analytic_jet_center_sound = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_analytic_domain
       (candle_q_center_environment_list boxes) e
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_q_dim_analytic_jet
         (candle_q_center_environment_list boxes) e)
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let length_th =
    ASSUME
      `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
       dimindex (:N)` in
  let stack_th =
    MATCH_MP
      (ISPEC `boxes:(((num#num)#num)#((num#num)#num))list`
        candle_q_center_environment_vector_contains)
      length_th in
  let sound_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `candle_q_center_environment_list
           (boxes:(((num#num)#num)#((num#num)#num))list)`;
         `list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))`]
        candle_q_dim_analytic_jet_sound)
      (CONJ stack_th
        (ASSUME
          `candle_q_dim_analytic_domain
            (candle_q_center_environment_list boxes) e`)) in
  ACCEPT_TAC
    (REWRITE_RULE[candle_q_center_environment_list_length; length_th]
      sound_th));;

let candle_q_dim_analytic_jet_box_shape = prove
 (`!e boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_q_dim_analytic_jet boxes e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ACCEPT_TAC
    (REWRITE_RULE
      [ASSUME
        `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`]
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_shape)));;

let candle_q_dim_analytic_jet_box_sound = prove
 (`!e boxes.
     candle_q_dim_analytic_domain boxes e /\
     LENGTH boxes = dimindex (:N)
     ==>
     !(z:real^N). z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_q_dim_analytic_contains (dimindex (:N))
             (candle_q_dim_analytic_jet boxes e)
             (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  let length_th =
    ASSUME
      `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
       dimindex (:N)` in
  let stack_th =
    MATCH_MP
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`; `z:real^N`]
        candle_q_box_stack_contains_vector)
      (CONJ length_th
        (ASSUME
          `(z:real^N) IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]`)) in
  let sound_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `list_of_seq (\k. (z:real^N)$(k + 1)) (dimindex (:N))`]
        candle_q_dim_analytic_jet_sound)
      (CONJ stack_th
        (ASSUME `candle_q_dim_analytic_domain boxes e`)) in
  ACCEPT_TAC (REWRITE_RULE[length_th] sound_th));;

let candle_q_dim_analytic_jet_whole_box_upper_sound = prove
 (`!e boxes.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_analytic_domain
       (candle_q_center_environment_list boxes) e /\
     candle_q_dim_analytic_domain boxes e
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim e p <=
       candle_q_real
         (candle_q_dim_analytic_jet_whole_box_upper e boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_jet_whole_box_upper_def] THEN
  let length_th =
    ASSUME
      `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
       dimindex (:N)` in
  let center_shape_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_center_shape)
      length_th in
  let center_sound_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_center_sound)
      (CONJ length_th
        (ASSUME
          `candle_q_dim_analytic_domain
            (candle_q_center_environment_list boxes) e`)) in
  let box_shape_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_box_shape)
      length_th in
  let box_sound_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_box_sound)
      (CONJ
        (ASSUME `candle_q_dim_analytic_domain boxes e`) length_th) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `candle_q_dim_analytic_jet
           (candle_q_center_environment_list boxes) e`;
         `candle_q_dim_analytic_jet boxes e`]
        candle_q_dim_analytic_jet_taylor_upper_sound)
      (CONJ
        (ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`)
        (CONJ
          (ASSUME `candle_q_dim_analytic_domain boxes e`)
          (CONJ length_th
            (CONJ
              (ASSUME `candle_q_box_valid_list boxes`)
              (CONJ center_shape_th
                (CONJ center_sound_th
                  (CONJ box_shape_th box_sound_th)))))))));;

let candle_q_dim_analytic_jet_whole_box_accept_sound = prove
 (`!e boxes.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_analytic_jet_whole_box_numerical_accept e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim e p < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_jet_whole_box_numerical_accept_def] THEN
  STRIP_TAC THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
      (ISPECL
        [`e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_whole_box_upper_sound)
      (CONJ
        (ASSUME `candle_analytic_valid_dim (dimindex (:N)) e`)
        (CONJ
          (ASSUME
            `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
             dimindex (:N)`)
          (CONJ
            (ASSUME `candle_q_box_valid_list boxes`)
            (CONJ
              (ASSUME
                `candle_q_dim_analytic_domain
                  (candle_q_center_environment_list boxes) e`)
              (ASSUME `candle_q_dim_analytic_domain boxes e`))))) in
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
            (candle_q_dim_analytic_jet_whole_box_upper e boxes))`) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim e (p:real^N)`;
         `candle_q_real
           (candle_q_dim_analytic_jet_whole_box_upper e boxes)`;
         `&0`]
        REAL_LET_TRANS)
      (CONJ upper_at_p upper_negative)));;

end;;
