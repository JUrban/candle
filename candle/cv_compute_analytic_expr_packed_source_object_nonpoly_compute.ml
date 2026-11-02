(* ========================================================================== *)
(* Fail-closed executable replay of exact object-q nonpolynomial steps.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The state is transactional: malformed source *)
(* tags, stack underflow, short certificate streams, or failed certificate   *)
(* predicates return status zero with the original stack and stream.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_poly_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_nonpoly_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_nonpoly_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_atn_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_compute;;
open Candle_cv_analytic_expr_packed_source_object_item_compute;;
open Candle_cv_analytic_expr_packed_source_object_poly_compute;;

let candle_cv_q_packed_object_certificate_state_def = new_definition
 `candle_cv_q_packed_object_certificate_state success stack certificates =
    Cexp_pair (candle_cv_bool success) (Cexp_pair stack certificates)`;;

let candle_cv_q_packed_object_certificate_failure_def = new_definition
 `candle_cv_q_packed_object_certificate_failure stack certificates =
    candle_cv_q_packed_object_certificate_state F stack certificates`;;

let candle_cv_q_packed_object_certificate_from_execution_def = new_definition
 `candle_cv_q_packed_object_certificate_from_execution execution certificates =
    Cexp_pair (Cexp_fst execution)
      (Cexp_pair (Cexp_snd execution) certificates)`;;

let candle_cv_cval_list_has_def = define
 `(candle_cv_cval_list_has (Cexp_num 0) values = Cexp_num 1) /\
  (candle_cv_cval_list_has (Cexp_num (SUC n)) (Cexp_num m) =
     Cexp_num 0) /\
  (candle_cv_cval_list_has (Cexp_num (SUC n)) (Cexp_pair head tail) =
     candle_cv_cval_list_has (Cexp_num n) tail) /\
  (candle_cv_cval_list_has (Cexp_pair p q) values = Cexp_num 0)`;;

let candle_cv_cval_list_drop_def = define
 `(candle_cv_cval_list_drop (Cexp_num 0) values = values) /\
  (candle_cv_cval_list_drop (Cexp_num (SUC n)) (Cexp_num m) =
     Cexp_num 0) /\
  (candle_cv_cval_list_drop (Cexp_num (SUC n)) (Cexp_pair head tail) =
     candle_cv_cval_list_drop (Cexp_num n) tail) /\
  (candle_cv_cval_list_drop (Cexp_pair p q) values = Cexp_num 0)`;;

let candle_cv_cval_list_nth_def = new_definition
 `candle_cv_cval_list_nth position values =
    Cexp_fst (candle_cv_cval_list_drop position values)`;;

let candle_cv_q_packed_object_atn_denominator_def = new_definition
 `candle_cv_q_packed_object_atn_denominator square =
    candle_cv_q_interval_add candle_cv_q_atn_one_interval square`;;

let candle_cv_q_packed_object_atn_denominator_correct = prove
 (`!square.
     candle_cv_q_packed_object_atn_denominator
       (candle_cv_q_interval square) =
     candle_cv_q_interval
       (candle_q_packed_object_atn_denominator square)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_atn_denominator_def;
     candle_q_packed_object_atn_denominator_def;
     candle_cv_q_atn_one_interval_correct;
     candle_cv_q_interval_add_correct]);;

let candle_cv_q_packed_object_inv_step_def = new_definition
 `candle_cv_q_packed_object_inv_step radii certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (candle_cv_cval_list_has (Cexp_num 2) certificates)
        (let item = Cexp_fst stack in
         let center_reciprocal =
           candle_cv_cval_list_nth (Cexp_num 0) certificates in
         let box_reciprocal =
           candle_cv_cval_list_nth (Cexp_num 1) certificates in
         let certificate_rest =
           candle_cv_cval_list_drop (Cexp_num 2) certificates in
         Cexp_if
           (candle_cv_bool_and
             (candle_cv_q_interval_inv_certificate
               (candle_cv_q_packed_object_state_center_value item)
               center_reciprocal)
             (candle_cv_q_interval_inv_certificate
               (candle_cv_q_packed_object_state_value_bound item)
               box_reciprocal))
           (candle_cv_q_packed_object_certificate_state T
             (Cexp_pair
               (candle_cv_q_packed_object_state_inverse radii
                 center_reciprocal box_reciprocal item)
               (Cexp_snd stack))
             certificate_rest)
           (candle_cv_q_packed_object_certificate_failure
             stack certificates))
        (candle_cv_q_packed_object_certificate_failure stack certificates))
      (candle_cv_q_packed_object_certificate_failure stack certificates)`;;

let candle_cv_q_packed_object_sqrt_step_def = new_definition
 `candle_cv_q_packed_object_sqrt_step radii certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (candle_cv_cval_list_has (Cexp_num 5) certificates)
        (let item = Cexp_fst stack in
         let center_root =
           candle_cv_cval_list_nth (Cexp_num 0) certificates in
         let box_root =
           candle_cv_cval_list_nth (Cexp_num 1) certificates in
         let center_derivative =
           candle_cv_cval_list_nth (Cexp_num 2) certificates in
         let box_derivative =
           candle_cv_cval_list_nth (Cexp_num 3) certificates in
         let box_second_reciprocal =
           candle_cv_cval_list_nth (Cexp_num 4) certificates in
         let certificate_rest =
           candle_cv_cval_list_drop (Cexp_num 5) certificates in
         Cexp_if
           (candle_cv_bool_and
             (candle_cv_q_interval_sqrt_certificate
               (candle_cv_q_packed_object_state_center_value item)
               center_root)
             (candle_cv_bool_and
               (candle_cv_q_interval_inv_certificate
                 (candle_cv_q_interval_add center_root center_root)
                 center_derivative)
               (candle_cv_bool_and
                 (candle_cv_q_interval_sqrt_certificate
                   (candle_cv_q_packed_object_state_value_bound item)
                   box_root)
                 (candle_cv_bool_and
                   (candle_cv_q_interval_inv_certificate
                     (candle_cv_q_interval_add box_root box_root)
                     box_derivative)
                   (candle_cv_q_interval_inv_certificate
                     (candle_cv_q_interval_mul
                       (candle_cv_q_interval_add box_root box_root)
                       (candle_cv_q_interval_add
                         (candle_cv_q_packed_object_state_value_bound item)
                         (candle_cv_q_packed_object_state_value_bound item)))
                     box_second_reciprocal)))))
           (candle_cv_q_packed_object_certificate_state T
             (Cexp_pair
               (candle_cv_q_packed_object_state_sqrt radii center_root
                 center_derivative box_derivative box_second_reciprocal item)
               (Cexp_snd stack))
             certificate_rest)
           (candle_cv_q_packed_object_certificate_failure
             stack certificates))
        (candle_cv_q_packed_object_certificate_failure stack certificates))
      (candle_cv_q_packed_object_certificate_failure stack certificates)`;;

let candle_cv_q_packed_object_atn_step_def = new_definition
 `candle_cv_q_packed_object_atn_step radii certificates stack =
    Cexp_if (Cexp_ispair stack)
      (Cexp_if (candle_cv_cval_list_has (Cexp_num 8) certificates)
        (let item = Cexp_fst stack in
         let center_input =
           candle_cv_cval_list_nth (Cexp_num 0) certificates in
         let box_input =
           candle_cv_cval_list_nth (Cexp_num 1) certificates in
         let center_result =
           candle_cv_cval_list_nth (Cexp_num 2) certificates in
         let center_square =
           candle_cv_cval_list_nth (Cexp_num 3) certificates in
         let center_derivative =
           candle_cv_cval_list_nth (Cexp_num 4) certificates in
         let box_square =
           candle_cv_cval_list_nth (Cexp_num 5) certificates in
         let box_derivative =
           candle_cv_cval_list_nth (Cexp_num 6) certificates in
         let box_derivative_square =
           candle_cv_cval_list_nth (Cexp_num 7) certificates in
         let certificate_rest =
           candle_cv_cval_list_drop (Cexp_num 8) certificates in
         Cexp_if
           (candle_cv_bool_and
             (candle_cv_q_interval_atn_outer_certificate
               (candle_cv_q_packed_object_state_center_value item)
               center_input center_result)
             (candle_cv_bool_and
               (candle_cv_q_interval_square_outer_certificate
                 (candle_cv_q_packed_object_state_center_value item)
                 center_input center_square)
               (candle_cv_bool_and
                 (candle_cv_q_interval_inv_certificate
                   (candle_cv_q_packed_object_atn_denominator center_square)
                   center_derivative)
                 (candle_cv_bool_and
                   (candle_cv_q_interval_square_outer_certificate
                     (candle_cv_q_packed_object_state_value_bound item)
                     box_input box_square)
                   (candle_cv_bool_and
                     (candle_cv_q_interval_inv_certificate
                       (candle_cv_q_packed_object_atn_denominator box_square)
                       box_derivative)
                     (candle_cv_q_interval_square_outer_certificate
                       box_derivative box_derivative
                       box_derivative_square))))))
           (candle_cv_q_packed_object_certificate_state T
             (Cexp_pair
               (candle_cv_q_packed_object_state_atn radii center_result
                 center_derivative box_derivative box_derivative_square item)
               (Cexp_snd stack))
             certificate_rest)
           (candle_cv_q_packed_object_certificate_failure
             stack certificates))
        (candle_cv_q_packed_object_certificate_failure stack certificates))
      (candle_cv_q_packed_object_certificate_failure stack certificates)`;;

let candle_cv_q_packed_object_nonpoly_step_def = new_definition
 `candle_cv_q_packed_object_nonpoly_step center_boxes outer_boxes radii
      source certificates stack =
    Cexp_if (Cexp_ispair source)
      (Cexp_if (Cexp_eq (Cexp_fst source) (Cexp_num 1))
        (candle_cv_q_packed_object_sqrt_step radii certificates stack)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
      (Cexp_if (Cexp_eq source (Cexp_num 2))
        (candle_cv_q_packed_object_certificate_from_execution
          (candle_cv_q_packed_object_poly_step center_boxes outer_boxes radii
            source stack)
          certificates)
        (Cexp_if (Cexp_eq source (Cexp_num 3))
          (candle_cv_q_packed_object_certificate_from_execution
            (candle_cv_q_packed_object_poly_step center_boxes outer_boxes
              radii source stack)
            certificates)
          (Cexp_if (Cexp_eq source (Cexp_num 4))
            (candle_cv_q_packed_object_certificate_from_execution
              (candle_cv_q_packed_object_poly_step center_boxes outer_boxes
                radii source stack)
              certificates)
            (Cexp_if (Cexp_eq source (Cexp_num 5))
              (candle_cv_q_packed_object_certificate_from_execution
                (candle_cv_q_packed_object_poly_step center_boxes outer_boxes
                  radii source stack)
                certificates)
              (Cexp_if (Cexp_eq source (Cexp_num 6))
                (candle_cv_q_packed_object_inv_step
                  radii certificates stack)
                (Cexp_if (Cexp_eq source (Cexp_num 7))
                  (candle_cv_q_packed_object_atn_step
                    radii certificates stack)
                  (Cexp_if (Cexp_eq source (Cexp_num 8))
                    (candle_cv_q_packed_object_certificate_state T
                      (Cexp_pair
                        candle_cv_q_packed_object_pi_half_state stack)
                      certificates)
                    (candle_cv_q_packed_object_certificate_failure
                      stack certificates))))))))`;;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE definitions";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_atn_denominator_correct] then
  failwith "packed object nonpoly compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_NONPOLY_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
