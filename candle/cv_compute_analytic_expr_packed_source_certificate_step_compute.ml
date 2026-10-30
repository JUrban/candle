(* ========================================================================== *)
(* Executable nonlinear steps for certificate-driven packed source replay.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The semantic source stack also records the    *)
(* analytic expression represented by every node.  Execution needs only the *)
(* exact Taylor results, so this layer runs on their projection and proves   *)
(* that every successful nonlinear source step has exactly that projection.  *)
(* Malformed stacks or certificate streams fail closed.                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certificate_result_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_step_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_sqrt;;
open Candle_cv_analytic_expr_packed_source_certified_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_result_compute;;

let candle_q_packed_source_item_results_def = new_definition
 `candle_q_packed_source_item_results items =
    MAP candle_q_packed_source_item_result items`;;

let candle_cv_q_packed_source_certificate_state_def = new_definition
 `candle_cv_q_packed_source_certificate_state valid stack certificates =
    Cexp_pair (candle_cv_bool valid) (Cexp_pair stack certificates)`;;

let candle_cv_q_packed_source_certificate_failure_def = new_definition
 `candle_cv_q_packed_source_certificate_failure stack certificates =
    candle_cv_q_packed_source_certificate_state F stack certificates`;;

let candle_cv_q_dim_jet_atn_denominator_with_square_def = new_definition
 `candle_cv_q_dim_jet_atn_denominator_with_square square =
    candle_cv_q_interval_add_normalized
      candle_cv_q_atn_one_interval square`;;

let candle_cv_q_dim_jet_atn_denominator_with_square_correct = prove
 (`!square.
     candle_cv_q_dim_jet_atn_denominator_with_square
       (candle_cv_q_interval square) =
     candle_cv_q_interval
       (candle_q_dim_jet_atn_denominator_with_square square)`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_atn_denominator_with_square_def;
     candle_q_dim_jet_atn_denominator_with_square_def;
     candle_cv_q_atn_one_interval_correct;
     candle_cv_q_interval_add_normalized_correct]);;

(* The executable state is deliberately transactional: on any failed shape *)
(* or certificate check it returns the original stack and stream with a zero *)
(* status.  The whole-program entry accepts only a final status of one.       *)

let candle_cv_q_packed_source_certificate_inv_step_def = new_definition
 `candle_cv_q_packed_source_certificate_inv_step boxes certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (Cexp_ispair certificates)
        (Cexp_if (Cexp_ispair (Cexp_snd certificates))
          (let result = Cexp_fst stack in
           let center_reciprocal = Cexp_fst certificates in
           let box_reciprocal = Cexp_fst (Cexp_snd certificates) in
           let certificate_rest = Cexp_snd (Cexp_snd certificates) in
           let valid =
             candle_cv_bool_and
               (candle_cv_q_interval_inv_certificate
                 (candle_cv_q_dim_first_jet_f
                   (candle_cv_q_dim_taylor_model_result_center result))
                 center_reciprocal)
               (candle_cv_q_interval_inv_certificate
                 (candle_cv_q_dim_jet_f
                   (candle_cv_q_dim_taylor_model_proxy result))
                 box_reciprocal) in
           Cexp_if valid
             (candle_cv_q_packed_source_certificate_state T
               (Cexp_pair
                 (candle_cv_q_dim_taylor_model_result_inv_certified
                   (candle_cv_q_fixed_list_round_upper
                     (candle_cv_q_radius_list boxes))
                   center_reciprocal box_reciprocal result)
                 (Cexp_snd stack))
               certificate_rest)
             (candle_cv_q_packed_source_certificate_failure
               stack certificates))
          (candle_cv_q_packed_source_certificate_failure stack certificates))
        (candle_cv_q_packed_source_certificate_failure stack certificates))
      (candle_cv_q_packed_source_certificate_failure stack certificates)`;;

let candle_cv_q_packed_source_certificate_sqrt_step_def = new_definition
 `candle_cv_q_packed_source_certificate_sqrt_step boxes certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (Cexp_ispair certificates)
        (Cexp_if (Cexp_ispair (Cexp_snd certificates))
          (Cexp_if (Cexp_ispair (Cexp_snd (Cexp_snd certificates)))
            (Cexp_if
              (Cexp_ispair
                (Cexp_snd (Cexp_snd (Cexp_snd certificates))))
              (Cexp_if
                (Cexp_ispair
                  (Cexp_snd
                    (Cexp_snd (Cexp_snd (Cexp_snd certificates)))))
                (let result = Cexp_fst stack in
                 let center_root = Cexp_fst certificates in
                 let box_root = Cexp_fst (Cexp_snd certificates) in
                 let center_derivative =
                   Cexp_fst (Cexp_snd (Cexp_snd certificates)) in
                 let box_derivative =
                   Cexp_fst
                     (Cexp_snd (Cexp_snd (Cexp_snd certificates))) in
                 let box_second_reciprocal =
                   Cexp_fst
                     (Cexp_snd
                       (Cexp_snd
                         (Cexp_snd (Cexp_snd certificates)))) in
                 let certificate_rest =
                   Cexp_snd
                     (Cexp_snd
                       (Cexp_snd
                         (Cexp_snd (Cexp_snd certificates)))) in
                 let valid =
                   candle_cv_bool_and
                     (candle_cv_q_interval_sqrt_certificate
                       (candle_cv_q_dim_first_jet_f
                         (candle_cv_q_dim_taylor_model_result_center result))
                       center_root)
                     (candle_cv_bool_and
                       (candle_cv_q_interval_inv_certificate
                         (candle_cv_q_interval_add_normalized
                           center_root center_root)
                         center_derivative)
                       (candle_cv_q_dim_jet_sqrt_certificates
                         (candle_cv_q_dim_jet_f
                           (candle_cv_q_dim_taylor_model_proxy result))
                         box_root box_derivative
                         box_second_reciprocal)) in
                 Cexp_if valid
                   (candle_cv_q_packed_source_certificate_state T
                     (Cexp_pair
                       (candle_cv_q_dim_taylor_model_result_sqrt_certified
                         (candle_cv_q_fixed_list_round_upper
                           (candle_cv_q_radius_list boxes))
                         center_root box_root center_derivative box_derivative
                         box_second_reciprocal result)
                       (Cexp_snd stack))
                     certificate_rest)
                   (candle_cv_q_packed_source_certificate_failure
                     stack certificates))
                (candle_cv_q_packed_source_certificate_failure
                  stack certificates))
              (candle_cv_q_packed_source_certificate_failure
                stack certificates))
            (candle_cv_q_packed_source_certificate_failure stack certificates))
          (candle_cv_q_packed_source_certificate_failure stack certificates))
        (candle_cv_q_packed_source_certificate_failure stack certificates))
      (candle_cv_q_packed_source_certificate_failure stack certificates)`;;

let candle_cv_q_packed_source_certificate_atn_step_def = new_definition
 `candle_cv_q_packed_source_certificate_atn_step boxes certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (Cexp_ispair certificates)
        (Cexp_if (Cexp_ispair (Cexp_snd certificates))
          (Cexp_if (Cexp_ispair (Cexp_snd (Cexp_snd certificates)))
            (Cexp_if
              (Cexp_ispair
                (Cexp_snd (Cexp_snd (Cexp_snd certificates))))
              (Cexp_if
                (Cexp_ispair
                  (Cexp_snd
                    (Cexp_snd (Cexp_snd (Cexp_snd certificates)))))
                (Cexp_if
                  (Cexp_ispair
                    (Cexp_snd
                      (Cexp_snd
                        (Cexp_snd
                          (Cexp_snd (Cexp_snd certificates))))))
                  (Cexp_if
                    (Cexp_ispair
                      (Cexp_snd
                        (Cexp_snd
                          (Cexp_snd
                            (Cexp_snd
                              (Cexp_snd (Cexp_snd certificates)))))))
                    (Cexp_if
                      (Cexp_ispair
                        (Cexp_snd
                          (Cexp_snd
                            (Cexp_snd
                              (Cexp_snd
                                (Cexp_snd
                                  (Cexp_snd (Cexp_snd certificates))))))))
                      (let result = Cexp_fst stack in
                       let center_input = Cexp_fst certificates in
                       let box_input = Cexp_fst (Cexp_snd certificates) in
                       let center_result =
                         Cexp_fst (Cexp_snd (Cexp_snd certificates)) in
                       let center_square =
                         Cexp_fst
                           (Cexp_snd
                             (Cexp_snd (Cexp_snd certificates))) in
                       let center_derivative =
                         Cexp_fst
                           (Cexp_snd
                             (Cexp_snd
                               (Cexp_snd (Cexp_snd certificates)))) in
                       let box_square =
                         Cexp_fst
                           (Cexp_snd
                             (Cexp_snd
                               (Cexp_snd
                                 (Cexp_snd (Cexp_snd certificates))))) in
                       let box_derivative =
                         Cexp_fst
                           (Cexp_snd
                             (Cexp_snd
                               (Cexp_snd
                                 (Cexp_snd
                                   (Cexp_snd (Cexp_snd certificates)))))) in
                       let box_derivative_square =
                         Cexp_fst
                           (Cexp_snd
                             (Cexp_snd
                               (Cexp_snd
                                 (Cexp_snd
                                   (Cexp_snd
                                     (Cexp_snd
                                       (Cexp_snd certificates))))))) in
                       let certificate_rest =
                         Cexp_snd
                           (Cexp_snd
                             (Cexp_snd
                               (Cexp_snd
                                 (Cexp_snd
                                   (Cexp_snd
                                     (Cexp_snd
                                       (Cexp_snd certificates))))))) in
                       let center_value =
                         candle_cv_q_dim_first_jet_f
                           (candle_cv_q_dim_taylor_model_result_center result) in
                       let box_value =
                         candle_cv_q_dim_jet_f
                           (candle_cv_q_dim_taylor_model_proxy result) in
                       let valid =
                         candle_cv_bool_and
                           (candle_cv_q_interval_atn_outer_certificate
                             center_value center_input center_result)
                           (candle_cv_bool_and
                             (candle_cv_q_interval_square_outer_certificate
                               center_value center_input center_square)
                             (candle_cv_bool_and
                               (candle_cv_q_interval_inv_certificate
                                 (candle_cv_q_dim_jet_atn_denominator_with_square
                                   center_square)
                                 center_derivative)
                               (candle_cv_bool_and
                                 (candle_cv_q_interval_square_outer_certificate
                                   box_value box_input box_square)
                                 (candle_cv_bool_and
                                   (candle_cv_q_interval_inv_certificate
                                     (candle_cv_q_dim_jet_atn_denominator_with_square
                                       box_square)
                                     box_derivative)
                                   (candle_cv_q_interval_square_outer_certificate
                                     box_derivative box_derivative
                                     box_derivative_square))))) in
                       Cexp_if valid
                         (candle_cv_q_packed_source_certificate_state T
                           (Cexp_pair
                             (candle_cv_q_dim_taylor_model_result_atn_faithful
                               (candle_cv_q_fixed_list_round_upper
                                 (candle_cv_q_radius_list boxes))
                               box_input center_result center_derivative
                               box_derivative box_derivative_square result)
                             (Cexp_snd stack))
                           certificate_rest)
                         (candle_cv_q_packed_source_certificate_failure
                           stack certificates))
                      (candle_cv_q_packed_source_certificate_failure
                        stack certificates))
                    (candle_cv_q_packed_source_certificate_failure
                      stack certificates))
                  (candle_cv_q_packed_source_certificate_failure
                    stack certificates))
                (candle_cv_q_packed_source_certificate_failure
                  stack certificates))
              (candle_cv_q_packed_source_certificate_failure
                stack certificates))
            (candle_cv_q_packed_source_certificate_failure stack certificates))
          (candle_cv_q_packed_source_certificate_failure stack certificates))
        (candle_cv_q_packed_source_certificate_failure stack certificates))
      (candle_cv_q_packed_source_certificate_failure stack certificates)`;;

let _ = print_endline "CANDLE_CERT_STEP_STAGE definitions";;

let candle_q_packed_source_item_results_cons = prove
 (`!item rest.
     candle_q_packed_source_item_results (CONS item rest) =
     CONS (candle_q_packed_source_item_result item)
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC[candle_q_packed_source_item_results_def; MAP]);;

let candle_q_interval_not_all_neq = prove
 (`!interval:((num#num)#num)#((num#num)#num).
     ~(!candidate. ~(interval = candidate))`,
  MESON_TAC[]);;

let candle_q_packed_source_item_results_inv_certified = prove
 (`!boxes center_reciprocal box_reciprocal item rest.
     candle_q_packed_source_item_results
       (CONS
         (candle_q_packed_source_item_inv_certified boxes
           center_reciprocal box_reciprocal item) rest) =
     CONS
       (candle_q_dim_taylor_model_result_inv_certified
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         center_reciprocal box_reciprocal
         (candle_q_packed_source_item_result item))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_inv_certified_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE inv-projection";;

let candle_cv_q_packed_source_certificate_inv_step_shape = prove
 (`!boxes item rest center_reciprocal box_reciprocal certificate_rest.
     candle_cv_q_packed_source_certificate_inv_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_reciprocal
           (CONS box_reciprocal certificate_rest)))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     let result = candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_source_item_result item) in
     let center_reciprocal_cv = candle_cv_q_interval center_reciprocal in
     let box_reciprocal_cv = candle_cv_q_interval box_reciprocal in
     let valid =
       candle_cv_bool_and
         (candle_cv_q_interval_inv_certificate
           (candle_cv_q_dim_first_jet_f
             (candle_cv_q_dim_taylor_model_result_center result))
           center_reciprocal_cv)
         (candle_cv_q_interval_inv_certificate
           (candle_cv_q_dim_jet_f
             (candle_cv_q_dim_taylor_model_proxy result))
           box_reciprocal_cv) in
     Cexp_if valid
       (candle_cv_q_packed_source_certificate_state T
         (Cexp_pair
           (candle_cv_q_dim_taylor_model_result_inv_certified
             (candle_cv_q_fixed_list_round_upper
               (candle_cv_q_radius_list
                 (candle_cv_q_interval_list boxes)))
             center_reciprocal_cv box_reciprocal_cv result)
           (candle_cv_q_dim_taylor_model_result_list_encode
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_reciprocal
             (CONS box_reciprocal certificate_rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_inv_step_def;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_interval_list_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE inv-shape";;

let candle_cv_q_packed_source_certificate_inv_step_encoded = prove
 (`!boxes item rest center_reciprocal box_reciprocal certificate_rest.
     candle_cv_q_packed_source_certificate_inv_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_reciprocal
           (CONS box_reciprocal certificate_rest)))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     Cexp_if
       (candle_cv_bool
         (candle_q_interval_inv_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_result_center
               (candle_q_packed_source_item_result item)))
           center_reciprocal /\
          candle_q_interval_inv_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_proxy
               (candle_q_packed_source_item_result item)))
           box_reciprocal))
       (candle_cv_q_packed_source_certificate_state T
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS
             (candle_q_dim_taylor_model_result_inv_certified
               (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
               center_reciprocal box_reciprocal
               (candle_q_packed_source_item_result item))
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_reciprocal
             (CONS box_reciprocal certificate_rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_inv_step_shape;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_f_correct;
     candle_q_dim_jet_f_def;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_f_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     candle_cv_q_dim_taylor_model_result_inv_certified_correct;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE inv-encoded";;

let candle_cv_q_packed_source_certificate_inv_step_success = prove
 (`!boxes item rest center_reciprocal box_reciprocal certificate_rest.
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item))) center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item))) box_reciprocal
     ==>
     candle_cv_q_packed_source_certificate_inv_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_reciprocal
           (CONS box_reciprocal certificate_rest)))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS
           (candle_q_dim_taylor_model_result_inv_certified
             (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
             center_reciprocal box_reciprocal
             (candle_q_packed_source_item_result item))
           (candle_q_packed_source_item_results rest)))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_source_certificate_inv_step_encoded;
     candle_cv_bool_def; cexp_if_def]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE inv-success";;

let candle_cv_q_packed_source_certificate_inv_step_refines = prove
 (`!boxes certificates stack next certificate_rest.
     candle_q_packed_source_certificate_step boxes
       Candle_analytic_program_inv certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_source_certificate_inv_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results next))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_item_results_cons;
     candle_q_packed_source_item_results_inv_certified] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_inv_step_success THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE inv";;

let candle_q_packed_source_item_results_sqrt_certified = prove
 (`!boxes center_root box_root center_derivative box_derivative
       box_second_reciprocal item rest.
     candle_q_packed_source_item_results
       (CONS
         (candle_q_packed_source_item_sqrt_certified boxes
           center_root box_root center_derivative box_derivative
           box_second_reciprocal item) rest) =
     CONS
       (candle_q_dim_taylor_model_result_sqrt_certified
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         center_root box_root center_derivative box_derivative
         box_second_reciprocal
         (candle_q_packed_source_item_result item))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_sqrt_certified_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE sqrt-projection";;

let candle_cv_q_packed_source_certificate_sqrt_step_shape = prove
 (`!boxes item rest center_root box_root center_derivative box_derivative
       box_second_reciprocal certificate_rest.
     candle_cv_q_packed_source_certificate_sqrt_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     let result = candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_source_item_result item) in
     let center_root_cv = candle_cv_q_interval center_root in
     let box_root_cv = candle_cv_q_interval box_root in
     let center_derivative_cv = candle_cv_q_interval center_derivative in
     let box_derivative_cv = candle_cv_q_interval box_derivative in
     let box_second_reciprocal_cv =
       candle_cv_q_interval box_second_reciprocal in
     let valid =
       candle_cv_bool_and
         (candle_cv_q_interval_sqrt_certificate
           (candle_cv_q_dim_first_jet_f
             (candle_cv_q_dim_taylor_model_result_center result))
           center_root_cv)
         (candle_cv_bool_and
           (candle_cv_q_interval_inv_certificate
             (candle_cv_q_interval_add_normalized
               center_root_cv center_root_cv)
             center_derivative_cv)
           (candle_cv_q_dim_jet_sqrt_certificates
             (candle_cv_q_dim_jet_f
               (candle_cv_q_dim_taylor_model_proxy result))
             box_root_cv box_derivative_cv
             box_second_reciprocal_cv)) in
     Cexp_if valid
       (candle_cv_q_packed_source_certificate_state T
         (Cexp_pair
           (candle_cv_q_dim_taylor_model_result_sqrt_certified
             (candle_cv_q_fixed_list_round_upper
               (candle_cv_q_radius_list
                 (candle_cv_q_interval_list boxes)))
             center_root_cv box_root_cv center_derivative_cv
             box_derivative_cv box_second_reciprocal_cv result)
           (candle_cv_q_dim_taylor_model_result_list_encode
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_root
             (CONS box_root
               (CONS center_derivative
                 (CONS box_derivative
                   (CONS box_second_reciprocal certificate_rest)))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_sqrt_step_def;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_interval_list_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE sqrt-shape";;

let candle_cv_q_packed_source_certificate_sqrt_step_encoded = prove
 (`!boxes item rest center_root box_root center_derivative box_derivative
       box_second_reciprocal certificate_rest.
     candle_cv_q_packed_source_certificate_sqrt_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     Cexp_if
       (candle_cv_bool
         (candle_q_interval_sqrt_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_result_center
               (candle_q_packed_source_item_result item))) center_root /\
          candle_q_interval_inv_certificate
           (candle_q_interval_add_normalized center_root center_root)
           center_derivative /\
          candle_q_dim_jet_sqrt_certificates
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_proxy
               (candle_q_packed_source_item_result item)))
           box_root box_derivative box_second_reciprocal))
       (candle_cv_q_packed_source_certificate_state T
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS
             (candle_q_dim_taylor_model_result_sqrt_certified
               (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
               center_root box_root center_derivative box_derivative
               box_second_reciprocal
               (candle_q_packed_source_item_result item))
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_root
             (CONS box_root
               (CONS center_derivative
                 (CONS box_derivative
                   (CONS box_second_reciprocal certificate_rest)))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_sqrt_step_shape;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_f_correct;
     candle_q_dim_jet_f_def;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_f_correct;
     candle_cv_q_interval_sqrt_certificate_bool_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_q_interval_add_normalized_correct;
     candle_cv_q_dim_jet_sqrt_certificates_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     candle_cv_q_dim_taylor_model_result_sqrt_certified_correct;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE sqrt-encoded";;

let candle_cv_q_packed_source_certificate_sqrt_step_success = prove
 (`!boxes item rest center_root box_root center_derivative box_derivative
       box_second_reciprocal certificate_rest.
     candle_q_interval_sqrt_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item))) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized center_root center_root)
       center_derivative /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_root box_derivative box_second_reciprocal
     ==>
     candle_cv_q_packed_source_certificate_sqrt_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS
           (candle_q_dim_taylor_model_result_sqrt_certified
             (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
             center_root box_root center_derivative box_derivative
             box_second_reciprocal
             (candle_q_packed_source_item_result item))
           (candle_q_packed_source_item_results rest)))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_source_certificate_sqrt_step_encoded;
     candle_cv_bool_def; cexp_if_def]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE sqrt-success";;

let candle_cv_q_packed_source_certificate_sqrt_step_refines = prove
 (`!boxes source_sqrt certificates stack next certificate_rest.
     candle_q_packed_source_certificate_step boxes
       (Candle_analytic_program_sqrt source_sqrt)
       certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_source_certificate_sqrt_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results next))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction";
              injectivity "candle_analytic_instruction";
              candle_q_interval_not_all_neq] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_item_results_cons;
     candle_q_packed_source_item_results_sqrt_certified] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_sqrt_step_success THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE sqrt";;

let candle_q_packed_source_item_results_atn_faithful = prove
 (`!boxes center_input box_input center_result center_square
       center_derivative box_square box_derivative box_derivative_square
       item rest.
     candle_q_packed_source_item_results
       (CONS
         (candle_q_packed_source_item_atn_faithful boxes
           center_input box_input center_result center_square
           center_derivative box_square box_derivative
           box_derivative_square item) rest) =
     CONS
       (candle_q_dim_taylor_model_result_atn_faithful
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         box_input center_result center_derivative box_derivative
         box_derivative_square
         (candle_q_packed_source_item_result item))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_atn_faithful_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE atn-projection";;

let candle_cv_q_packed_source_certificate_atn_step_shape = prove
 (`!boxes item rest center_input box_input center_result center_square
       center_derivative box_square box_derivative box_derivative_square
       certificate_rest.
     candle_cv_q_packed_source_certificate_atn_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest)))))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     let result = candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_source_item_result item) in
     let center_input_cv = candle_cv_q_interval center_input in
     let box_input_cv = candle_cv_q_interval box_input in
     let center_result_cv = candle_cv_q_interval center_result in
     let center_square_cv = candle_cv_q_interval center_square in
     let center_derivative_cv = candle_cv_q_interval center_derivative in
     let box_square_cv = candle_cv_q_interval box_square in
     let box_derivative_cv = candle_cv_q_interval box_derivative in
     let box_derivative_square_cv =
       candle_cv_q_interval box_derivative_square in
     let center_value =
       candle_cv_q_dim_first_jet_f
         (candle_cv_q_dim_taylor_model_result_center result) in
     let box_value =
       candle_cv_q_dim_jet_f
         (candle_cv_q_dim_taylor_model_proxy result) in
     let valid =
       candle_cv_bool_and
         (candle_cv_q_interval_atn_outer_certificate
           center_value center_input_cv center_result_cv)
         (candle_cv_bool_and
           (candle_cv_q_interval_square_outer_certificate
             center_value center_input_cv center_square_cv)
           (candle_cv_bool_and
             (candle_cv_q_interval_inv_certificate
               (candle_cv_q_dim_jet_atn_denominator_with_square
                 center_square_cv)
               center_derivative_cv)
             (candle_cv_bool_and
               (candle_cv_q_interval_square_outer_certificate
                 box_value box_input_cv box_square_cv)
               (candle_cv_bool_and
                 (candle_cv_q_interval_inv_certificate
                   (candle_cv_q_dim_jet_atn_denominator_with_square
                     box_square_cv)
                   box_derivative_cv)
                 (candle_cv_q_interval_square_outer_certificate
                   box_derivative_cv box_derivative_cv
                   box_derivative_square_cv))))) in
     Cexp_if valid
       (candle_cv_q_packed_source_certificate_state T
         (Cexp_pair
           (candle_cv_q_dim_taylor_model_result_atn_faithful
             (candle_cv_q_fixed_list_round_upper
               (candle_cv_q_radius_list
                 (candle_cv_q_interval_list boxes)))
             box_input_cv center_result_cv center_derivative_cv
             box_derivative_cv box_derivative_square_cv result)
           (candle_cv_q_dim_taylor_model_result_list_encode
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_input
             (CONS box_input
               (CONS center_result
                 (CONS center_square
                   (CONS center_derivative
                     (CONS box_square
                       (CONS box_derivative
                         (CONS box_derivative_square
                           certificate_rest))))))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_atn_step_def;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_interval_list_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE atn-shape";;

let candle_cv_q_packed_source_certificate_atn_step_encoded = prove
 (`!boxes item rest center_input box_input center_result center_square
       center_derivative box_square box_derivative box_derivative_square
       certificate_rest.
     candle_cv_q_packed_source_certificate_atn_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest)))))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     Cexp_if
       (candle_cv_bool
         (candle_q_interval_atn_outer_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_result_center
               (candle_q_packed_source_item_result item)))
           center_input center_result /\
          candle_q_interval_square_outer_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_result_center
               (candle_q_packed_source_item_result item)))
           center_input center_square /\
          candle_q_interval_inv_certificate
           (candle_q_dim_jet_atn_denominator_with_square center_square)
           center_derivative /\
          candle_q_interval_square_outer_certificate
           (candle_q_dim_jet_f
             (candle_q_dim_taylor_model_proxy
               (candle_q_packed_source_item_result item)))
           box_input box_square /\
          candle_q_interval_inv_certificate
           (candle_q_dim_jet_atn_denominator_with_square box_square)
           box_derivative /\
          candle_q_interval_square_outer_certificate
           box_derivative box_derivative box_derivative_square))
       (candle_cv_q_packed_source_certificate_state T
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS
             (candle_q_dim_taylor_model_result_atn_faithful
               (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
               box_input center_result center_derivative box_derivative
               box_derivative_square
               (candle_q_packed_source_item_result item))
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list certificate_rest))
       (candle_cv_q_packed_source_certificate_failure
         (candle_cv_q_dim_taylor_model_result_list_encode
           (CONS (candle_q_packed_source_item_result item)
             (candle_q_packed_source_item_results rest)))
         (candle_cv_q_interval_list
           (CONS center_input
             (CONS box_input
               (CONS center_result
                 (CONS center_square
                   (CONS center_derivative
                     (CONS box_square
                       (CONS box_derivative
                         (CONS box_derivative_square
                           certificate_rest))))))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_atn_step_shape;
     candle_cv_q_dim_taylor_model_result_list_encode_def;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_f_correct;
     candle_q_dim_jet_f_def;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_f_correct;
     candle_cv_q_interval_atn_outer_certificate_correct;
     candle_cv_q_interval_square_outer_certificate_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_q_dim_jet_atn_denominator_with_square_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     candle_cv_q_dim_taylor_model_result_atn_faithful_correct;
     LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE atn-encoded";;

let candle_cv_q_packed_source_certificate_atn_step_success = prove
 (`!boxes item rest center_input box_input center_result center_square
       center_derivative box_square box_derivative box_derivative_square
       certificate_rest.
     candle_q_interval_atn_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_cv_q_packed_source_certificate_atn_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list
         (CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest)))))))))
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_source_item_result item)
           (candle_q_packed_source_item_results rest))) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS
           (candle_q_dim_taylor_model_result_atn_faithful
             (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
             box_input center_result center_derivative box_derivative
             box_derivative_square
             (candle_q_packed_source_item_result item))
           (candle_q_packed_source_item_results rest)))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_source_certificate_atn_step_encoded;
     candle_cv_bool_def; cexp_if_def]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE atn-success";;

let candle_cv_q_packed_source_certificate_atn_step_refines = prove
 (`!boxes certificates stack next certificate_rest.
     candle_q_packed_source_certificate_step boxes
       Candle_analytic_program_atn certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_source_certificate_atn_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results next))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_item_results_cons;
     candle_q_packed_source_item_results_atn_faithful] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_atn_step_success THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_CERT_STEP_STAGE atn";;

let candle_cv_q_packed_source_certificate_step_compute_eqs =
  union
    (map SPEC_ALL
      [candle_cv_q_packed_source_certificate_state_def;
       candle_cv_q_packed_source_certificate_failure_def;
       candle_cv_q_dim_jet_atn_denominator_with_square_def;
       candle_cv_q_packed_source_certificate_inv_step_def;
       candle_cv_q_packed_source_certificate_sqrt_step_def;
       candle_cv_q_packed_source_certificate_atn_step_def])
    candle_cv_q_packed_source_certificate_result_compute_eqs;;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_item_results_cons;
     candle_q_interval_not_all_neq;
     candle_q_packed_source_item_results_inv_certified;
     candle_cv_q_packed_source_certificate_inv_step_shape;
     candle_cv_q_packed_source_certificate_inv_step_encoded;
     candle_cv_q_packed_source_certificate_inv_step_success;
     candle_cv_q_packed_source_certificate_inv_step_refines;
     candle_q_packed_source_item_results_sqrt_certified;
     candle_cv_q_packed_source_certificate_sqrt_step_shape;
     candle_cv_q_packed_source_certificate_sqrt_step_encoded;
     candle_cv_q_packed_source_certificate_sqrt_step_success;
     candle_cv_q_packed_source_certificate_sqrt_step_refines;
     candle_q_packed_source_item_results_atn_faithful;
     candle_cv_q_packed_source_certificate_atn_step_shape;
     candle_cv_q_packed_source_certificate_atn_step_encoded;
     candle_cv_q_packed_source_certificate_atn_step_success;
     candle_cv_q_packed_source_certificate_atn_step_refines] then
  failwith "packed source certificate step compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_STEP_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
