(* ========================================================================== *)
(* Analytic whole-box checking with separate center and box certificates.     *)
(*                                                                            *)
(* The two compiled programs may carry different square-root enclosures, but *)
(* their certificate-erased expressions must be identical.  This lets the   *)
(* center use tight point certificates while the Hessian uses safe whole-box *)
(* certificates, without changing the represented Flyspeck source function.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_erasure.ml";;
needs "candle/cv_compute_analytic_expr_extended_taylor.ml";;
needs "candle/cv_compute_analytic_expr_first_center_check.ml";;

module Candle_cv_analytic_expr_split_certificate_check = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_taylor_sound;;
open Candle_cv_analytic_expr_jet_check;;
open Candle_cv_analytic_expr_first_center_check;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_extended_taylor;;

let candle_q_dim_analytic_split_certificate_upper_def = new_definition
 `candle_q_dim_analytic_split_certificate_upper center_e box_e boxes =
    candle_q_dim_taylor_upper_extended
      (candle_q_radius_list boxes)
      (candle_q_dim_jet_f
        (candle_q_dim_analytic_jet
          (candle_q_center_environment_list boxes) center_e))
      (candle_q_dim_jet_gradient
        (candle_q_dim_analytic_jet
          (candle_q_center_environment_list boxes) center_e))
      (candle_q_dim_jet_hessian
        (candle_q_dim_analytic_jet boxes box_e))`;;

let candle_q_dim_analytic_split_certificate_accept_def = new_definition
 `candle_q_dim_analytic_split_certificate_accept center_e box_e boxes <=>
    candle_q_box_valid_list boxes /\
    candle_q_dim_analytic_domain
      (candle_q_center_environment_list boxes) center_e /\
    candle_q_dim_analytic_domain boxes box_e /\
    candle_analytic_erase_sqrt_certificates center_e =
      candle_analytic_erase_sqrt_certificates box_e /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_analytic_split_certificate_upper
         center_e box_e boxes))`;;

let candle_cv_q_dim_analytic_split_certificate_upper_pair_def =
  new_definition
 `candle_cv_q_dim_analytic_split_certificate_upper_pair
      boxes center_result box_result =
    candle_cv_q_dim_taylor_upper_extended
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_dim_first_jet_f
        (candle_cv_q_dim_analytic_first_result_jet center_result))
      (candle_cv_q_dim_first_jet_gradient
        (candle_cv_q_dim_analytic_first_result_jet center_result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_analytic_result_jet box_result))`;;

let candle_cv_q_dim_analytic_split_certificate_finish_def = new_definition
 `candle_cv_q_dim_analytic_split_certificate_finish
      boxes center_result box_result =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_first_result_domain center_result)
        (candle_cv_q_dim_analytic_result_domain box_result))
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_analytic_split_certificate_upper_pair
        boxes center_result box_result)`;;

let candle_cv_q_dim_analytic_split_certificate_check_def = new_definition
 `candle_cv_q_dim_analytic_split_certificate_check
      center_program box_program boxes =
    candle_cv_q_dim_analytic_split_certificate_finish boxes
      (candle_cv_q_dim_analytic_first_program
        (candle_cv_q_center_environment_list boxes) center_program)
      (candle_cv_q_dim_analytic_program boxes box_program)`;;

let candle_cv_q_dim_analytic_split_certificate_upper_pair_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_split_certificate_upper_pair
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_first_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     candle_cv_q
       (candle_q_dim_taylor_upper_extended (candle_q_radius_list boxes)
         (candle_q_dim_analytic_result_jet center_result)
         (candle_q_dim_analytic_result_jet box_result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_split_certificate_upper_pair_def;
              candle_cv_q_dim_analytic_first_result_jet_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_upper_extended_correct]);;

let candle_cv_q_dim_analytic_split_certificate_finish_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_split_certificate_finish
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_first_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     Cexp_pair
       (Cexp_num
         (if candle_q_box_valid_list boxes /\
             candle_q_dim_analytic_result_domain center_result /\
             candle_q_dim_analytic_result_domain box_result /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_upper_extended
                  (candle_q_radius_list boxes)
                  (candle_q_dim_analytic_result_jet center_result)
                  (candle_q_dim_analytic_result_jet box_result)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_upper_extended (candle_q_radius_list boxes)
           (candle_q_dim_analytic_result_jet center_result)
           (candle_q_dim_analytic_result_jet box_result)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_split_certificate_finish_def;
              candle_cv_q_dim_analytic_first_result_domain_correct;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_bool_and_correct; candle_cv_bool_def;
              candle_cv_bool_and_def;
              candle_cv_q_box_valid_list_correct;
              candle_cv_q_dim_analytic_split_certificate_upper_pair_correct;
              candle_cv_q_dim_whole_box_finish_def;
              candle_cv_q_zero_def; candle_cv_q_le_correct;
              cexp_if_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_analytic_split_certificate_check_correct = prove
 (`!center_e box_e boxes.
     candle_cv_q_dim_analytic_split_certificate_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_box_valid_list boxes /\
             candle_q_dim_analytic_domain
               (candle_q_center_environment_list boxes) center_e /\
             candle_q_dim_analytic_domain boxes box_e /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_analytic_split_certificate_upper
                  center_e box_e boxes))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_analytic_split_certificate_upper
           center_e box_e boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_split_certificate_check_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_dim_analytic_first_compile_program_correct;
              candle_cv_q_dim_analytic_compile_program_correct;
              candle_cv_q_dim_analytic_split_certificate_finish_correct;
              candle_q_dim_analytic_result_domain_def;
              candle_q_dim_analytic_result_jet_def;
              candle_q_dim_analytic_split_certificate_upper_def]);;

let candle_cv_q_dim_analytic_split_certificate_compute_eqs =
  union candle_cv_q_extended_taylor_compute_eqs
    candle_cv_q_dim_analytic_first_center_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_analytic_split_certificate_upper_pair_def;
    candle_cv_q_dim_analytic_split_certificate_finish_def;
    candle_cv_q_dim_analytic_split_certificate_check_def];;

let candle_q_dim_analytic_split_certificate_upper_sound = prove
 (`!center_e box_e boxes.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_analytic_domain
       (candle_q_center_environment_list boxes) center_e /\
     candle_q_dim_analytic_domain boxes box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim box_e p <=
       candle_q_real
         (candle_q_dim_analytic_split_certificate_upper
           center_e box_e boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_split_certificate_upper_def] THEN
  let length_th =
    ASSUME
      `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
       dimindex (:N)` in
  let center_shape_th =
    MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_center_shape)
      length_th in
  let center_sound_center_e =
    MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_center_sound)
      (CONJ length_th
        (ASSUME
          `candle_q_dim_analytic_domain
            (candle_q_center_environment_list boxes) center_e`)) in
  let center_sound_box_e =
    let transport =
      MATCH_MP
        (ISPECL
          [`dimindex (:N)`;
           `candle_q_dim_analytic_jet
             (candle_q_center_environment_list boxes) center_e`;
           `list_of_seq
             (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
             (dimindex (:N))`;
           `center_e:candle_analytic_expr`;
           `box_e:candle_analytic_expr`]
          candle_q_dim_analytic_contains_certificate_transport)
        (ASSUME
          `candle_analytic_erase_sqrt_certificates center_e =
           candle_analytic_erase_sqrt_certificates box_e`) in
    EQ_MP transport center_sound_center_e in
  let box_shape_th =
    MATCH_MP
      (ISPECL
        [`box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_box_shape)
      length_th in
  let box_sound_th =
    MATCH_MP
      (ISPECL
        [`box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_jet_box_sound)
      (CONJ
        (ASSUME `candle_q_dim_analytic_domain boxes box_e`) length_th) in
  MP_TAC
    (MATCH_MP
      (ISPECL
        [`box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `candle_q_dim_analytic_jet
           (candle_q_center_environment_list boxes) center_e`;
         `candle_q_dim_analytic_jet boxes box_e`]
        candle_q_dim_analytic_jet_taylor_upper_sound)
      (CONJ
        (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_e`)
        (CONJ
          (ASSUME `candle_q_dim_analytic_domain boxes box_e`)
          (CONJ length_th
            (CONJ
              (ASSUME `candle_q_box_valid_list boxes`)
              (CONJ center_shape_th
                (CONJ center_sound_box_e
                  (CONJ box_shape_th box_sound_th)))))))) THEN
  REWRITE_TAC[candle_q_dim_taylor_upper_extended_real]);;

let candle_q_dim_analytic_split_certificate_accept_sound = prove
 (`!center_e box_e boxes.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_dim_analytic_split_certificate_accept
       center_e box_e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_split_certificate_accept_def] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
      (ISPECL
        [`center_e:candle_analytic_expr`;
         `box_e:candle_analytic_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_analytic_split_certificate_upper_sound)
      (CONJ
        (ASSUME `candle_analytic_valid_dim (dimindex (:N)) box_e`)
        (CONJ
          (ASSUME
            `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
             dimindex (:N)`)
          (CONJ
            (ASSUME `candle_q_box_valid_list boxes`)
            (CONJ
              (ASSUME
                `candle_q_dim_analytic_domain
                  (candle_q_center_environment_list boxes) center_e`)
              (CONJ
                (ASSUME `candle_q_dim_analytic_domain boxes box_e`)
                (ASSUME
                  `candle_analytic_erase_sqrt_certificates center_e =
                   candle_analytic_erase_sqrt_certificates box_e`)))))) in
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
            (candle_q_dim_analytic_split_certificate_upper
              center_e box_e boxes))`) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_analytic_denote_dim box_e (p:real^N)`;
         `candle_q_real
           (candle_q_dim_analytic_split_certificate_upper
             center_e box_e boxes)`;
         `&0`]
        REAL_LET_TRANS)
      (CONJ upper_at_p upper_negative)));;

end;;
