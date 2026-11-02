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
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
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

let candle_cv_q_packed_object_certificate_from_execution_correct = prove
 (`!success stack certificates.
     candle_cv_q_packed_object_certificate_from_execution
       (candle_cv_q_packed_object_execution_state success stack)
       certificates =
     candle_cv_q_packed_object_certificate_state
       success stack certificates`,
  REWRITE_TAC
    [candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     cexp_fst_def; cexp_snd_def]);;

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

let candle_cv_cval_one_suc = ARITH_RULE `1 = SUC 0`;;
let candle_cv_cval_two_suc = ARITH_RULE `2 = SUC 1`;;
let candle_cv_cval_three_suc = ARITH_RULE `3 = SUC 2`;;
let candle_cv_cval_four_suc = ARITH_RULE `4 = SUC 3`;;
let candle_cv_cval_five_suc = ARITH_RULE `5 = SUC 4`;;
let candle_cv_cval_six_suc = ARITH_RULE `6 = SUC 5`;;
let candle_cv_cval_seven_suc = ARITH_RULE `7 = SUC 6`;;
let candle_cv_cval_eight_suc = ARITH_RULE `8 = SUC 7`;;

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

let candle_cv_q_packed_object_nonpoly_neg_correct = prove
 (`!center_boxes outer_boxes radii certificates item rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_neg)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS (candle_q_packed_object_source_item_neg radii item) rest))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_poly_step
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_instruction Candle_q_neg)
      (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
    candle_cv_q_packed_object_execution_state T
      (candle_cv_q_packed_object_stack_encode
        (CONS (candle_q_packed_object_source_item_neg radii item) rest))`
  (LABEL_TAC "poly") THENL
   [MATCH_MP_TAC
      (SPECL
        [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         `item:candle_q_packed_object_item`;
         `rest:candle_q_packed_object_item list`]
        candle_cv_q_packed_object_poly_step_neg_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def; candle_cv_q_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    USE_THEN "poly"
      (fun theorem ->
        REWRITE_TAC[REWRITE_RULE[candle_cv_q_instruction_def] theorem]) THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_certificate_from_execution_correct]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE neg";;

let candle_cv_q_packed_object_nonpoly_add_correct = prove
 (`!center_boxes outer_boxes radii certificates left right rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_add)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode
         (CONS right (CONS left rest))) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_add radii left right) rest))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_poly_step
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_instruction Candle_q_add)
      (candle_cv_q_packed_object_stack_encode
        (CONS right (CONS left rest))) =
    candle_cv_q_packed_object_execution_state T
      (candle_cv_q_packed_object_stack_encode
        (CONS
          (candle_q_packed_object_source_item_add radii left right) rest))`
  (LABEL_TAC "poly") THENL
   [MATCH_MP_TAC
      (SPECL
        [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         `left:candle_q_packed_object_item`;
         `right:candle_q_packed_object_item`;
         `rest:candle_q_packed_object_item list`]
        candle_cv_q_packed_object_poly_step_add_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def; candle_cv_q_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    USE_THEN "poly"
      (fun theorem ->
        REWRITE_TAC[REWRITE_RULE[candle_cv_q_instruction_def] theorem]) THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_certificate_from_execution_correct]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE add";;

let candle_cv_q_packed_object_nonpoly_mul_correct = prove
 (`!center_boxes outer_boxes radii certificates left right rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_mul)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode
         (CONS right (CONS left rest))) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_mul radii left right) rest))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_poly_step
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_instruction Candle_q_mul)
      (candle_cv_q_packed_object_stack_encode
        (CONS right (CONS left rest))) =
    candle_cv_q_packed_object_execution_state T
      (candle_cv_q_packed_object_stack_encode
        (CONS
          (candle_q_packed_object_source_item_mul radii left right) rest))`
  (LABEL_TAC "poly") THENL
   [MATCH_MP_TAC
      (SPECL
        [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         `left:candle_q_packed_object_item`;
         `right:candle_q_packed_object_item`;
         `rest:candle_q_packed_object_item list`]
        candle_cv_q_packed_object_poly_step_mul_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def; candle_cv_q_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    USE_THEN "poly"
      (fun theorem ->
        REWRITE_TAC[REWRITE_RULE[candle_cv_q_instruction_def] theorem]) THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_certificate_from_execution_correct]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE mul";;

let candle_cv_q_packed_object_nonpoly_square_correct = prove
 (`!center_boxes outer_boxes radii certificates item rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_square)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_mul radii item item) rest))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_poly_step
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_instruction Candle_q_square)
      (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
    candle_cv_q_packed_object_execution_state T
      (candle_cv_q_packed_object_stack_encode
        (CONS
          (candle_q_packed_object_source_item_mul radii item item) rest))`
  (LABEL_TAC "poly") THENL
   [MATCH_MP_TAC
      (SPECL
        [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         `item:candle_q_packed_object_item`;
         `rest:candle_q_packed_object_item list`]
        candle_cv_q_packed_object_poly_step_square_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def; candle_cv_q_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    USE_THEN "poly"
      (fun theorem ->
        REWRITE_TAC[REWRITE_RULE[candle_cv_q_instruction_def] theorem]) THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_certificate_from_execution_correct]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE square";;

let candle_cv_q_packed_object_nonpoly_pi_half_correct = prove
 (`!center_boxes outer_boxes radii certificates stack.
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_pi_half)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS candle_q_packed_object_source_item_pi_half stack))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def;
     injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_pi_half_state_correct]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE pi_half";;

let candle_cv_q_packed_object_nonpoly_inverse_correct = prove
 (`!center_boxes outer_boxes radii item rest center_reciprocal
       box_reciprocal certificate_rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_center_value item)
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_value_bound item)
       box_reciprocal
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_inv)
       (candle_cv_q_interval_list
         (CONS center_reciprocal (CONS box_reciprocal certificate_rest)))
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_inverse radii
             center_reciprocal box_reciprocal item)
           rest))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_inverse
      (candle_cv_q_list radii)
      (candle_cv_q_interval center_reciprocal)
      (candle_cv_q_interval box_reciprocal)
      (candle_cv_q_packed_object_item_state_encode item) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_inverse radii
        center_reciprocal box_reciprocal item)`
  (LABEL_TAC "inverse") THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `center_reciprocal:((num#num)#num)#((num#num)#num)`;
         `box_reciprocal:((num#num)#num)#((num#num)#num)`;
         `item:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_inverse_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_inv_step_def;
       LET_DEF; LET_END_DEF;
       candle_cv_q_packed_object_stack_encode_def;
       candle_cv_q_interval_list_def;
       candle_cv_cval_one_suc; candle_cv_cval_two_suc;
       candle_cv_cval_three_suc; candle_cv_cval_four_suc;
       candle_cv_cval_five_suc; candle_cv_cval_six_suc;
       candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
       candle_cv_cval_list_has_def;
       candle_cv_cval_list_nth_def;
       candle_cv_cval_list_drop_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       candle_cv_q_packed_object_item_center_value_correct;
       candle_cv_q_packed_object_item_value_bound_correct;
       candle_cv_q_interval_inv_certificate_correct] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def; candle_cv_bool_def; cexp_if_def] THEN
    USE_THEN "inverse" (fun theorem -> REWRITE_TAC[theorem]) THEN
    REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE inverse";;

let candle_cv_q_packed_object_nonpoly_sqrt_correct = prove
 (`!center_boxes outer_boxes radii source_sqrt item rest center_root
       box_root center_derivative box_derivative box_second_reciprocal
       certificate_rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item /\
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_center_value item) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root)
       center_derivative /\
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_value_bound item) box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add
           (candle_q_packed_object_item_value_bound item)
           (candle_q_packed_object_item_value_bound item)))
       box_second_reciprocal
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction
         (Candle_analytic_program_sqrt source_sqrt))
       (candle_cv_q_interval_list
         (CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest))))))
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_sqrt radii center_root
             center_derivative box_root box_derivative
             box_second_reciprocal item)
           rest))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_sqrt
      (candle_cv_q_list radii)
      (candle_cv_q_interval center_root)
      (candle_cv_q_interval center_derivative)
      (candle_cv_q_interval box_derivative)
      (candle_cv_q_interval box_second_reciprocal)
      (candle_cv_q_packed_object_item_state_encode item) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_sqrt radii center_root
        center_derivative box_root box_derivative
        box_second_reciprocal item)`
  (LABEL_TAC "sqrt") THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `center_root:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`;
         `box_root:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_second_reciprocal:((num#num)#num)#((num#num)#num)`;
         `item:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_sqrt_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def;
       cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def] THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_sqrt_step_def;
       LET_DEF; LET_END_DEF;
       candle_cv_q_packed_object_stack_encode_def;
       candle_cv_q_interval_list_def;
       candle_cv_cval_one_suc; candle_cv_cval_two_suc;
       candle_cv_cval_three_suc; candle_cv_cval_four_suc;
       candle_cv_cval_five_suc; candle_cv_cval_six_suc;
       candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
       candle_cv_cval_list_has_def;
       candle_cv_cval_list_nth_def;
       candle_cv_cval_list_drop_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       candle_cv_q_packed_object_item_center_value_correct;
       candle_cv_q_packed_object_item_value_bound_correct;
       candle_cv_q_interval_add_correct;
       candle_cv_q_interval_mul_correct;
       candle_cv_q_interval_sqrt_certificate_correct;
       candle_cv_q_interval_inv_certificate_correct] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def; candle_cv_bool_def; cexp_if_def] THEN
    USE_THEN "sqrt" (fun theorem -> REWRITE_TAC[theorem]) THEN
    REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE sqrt";;

let candle_cv_q_packed_object_nonpoly_atn_correct = prove
 (`!center_boxes outer_boxes radii item rest
       (center_input:((num#num)#num)#((num#num)#num))
       (box_input:((num#num)#num)#((num#num)#num))
       center_result
       (center_square:((num#num)#num)#((num#num)#num)) center_derivative
       (box_square:((num#num)#num)#((num#num)#num))
       box_derivative box_derivative_square certificate_rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item /\
     candle_q_interval_atn_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_value_bound item)
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction Candle_analytic_program_atn)
       (candle_cv_q_interval_list
         (CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest)))))))))
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_atn radii center_input
             center_result center_square center_derivative box_input
             box_square box_derivative box_derivative_square item)
           rest))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_atn
      (candle_cv_q_list radii)
      (candle_cv_q_interval center_result)
      (candle_cv_q_interval center_derivative)
      (candle_cv_q_interval box_derivative)
      (candle_cv_q_interval box_derivative_square)
      (candle_cv_q_packed_object_item_state_encode item) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_atn radii center_input
        center_result center_square center_derivative box_input box_square
        box_derivative box_derivative_square item)`
  (LABEL_TAC "atn") THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`]
        candle_cv_q_packed_object_source_item_atn_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_nonpoly_step_def;
       candle_cv_analytic_instruction_def;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def] THEN
    REWRITE_TAC
      [candle_cv_q_packed_object_atn_step_def;
       LET_DEF; LET_END_DEF;
       candle_cv_q_packed_object_stack_encode_def;
       candle_cv_q_interval_list_def;
       candle_cv_cval_one_suc; candle_cv_cval_two_suc;
       candle_cv_cval_three_suc; candle_cv_cval_four_suc;
       candle_cv_cval_five_suc; candle_cv_cval_six_suc;
       candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
       candle_cv_cval_list_has_def;
       candle_cv_cval_list_nth_def;
       candle_cv_cval_list_drop_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       candle_cv_q_packed_object_item_center_value_correct;
       candle_cv_q_packed_object_item_value_bound_correct;
       candle_cv_q_packed_object_atn_denominator_correct;
       candle_cv_q_interval_atn_outer_certificate_correct;
       candle_cv_q_interval_square_outer_certificate_correct;
       candle_cv_q_interval_inv_certificate_correct] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def; candle_cv_bool_def; cexp_if_def] THEN
    USE_THEN "atn" (fun theorem -> REWRITE_TAC[theorem]) THEN
    REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def] THEN
    MP_TAC
      (SPEC `item:candle_q_packed_object_item`
        candle_q_packed_object_item_full_cases) THEN
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[candle_q_packed_object_source_item_atn_def]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE atn";;

let candle_cv_q_packed_object_nonpoly_step_correct = prove
 (`!center_boxes outer_boxes radii source certificates stack next
       certificate_rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_nonpoly_step
       radii source certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode next)
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
        (LABEL_TAC "step"))) THEN
  USE_THEN "step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_nonpoly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_neg_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_add_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_mul_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_square_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_inverse_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_sqrt_correct THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_atn_correct THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_cv_q_packed_object_nonpoly_pi_half_correct]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE generic_step";;

let candle_cv_q_packed_object_nonpoly_run_def = define
 `(candle_cv_q_packed_object_nonpoly_run center_boxes outer_boxes radii
      (Cexp_num n) execution = execution) /\
  (candle_cv_q_packed_object_nonpoly_run center_boxes outer_boxes radii
      (Cexp_pair source sources) execution =
    Cexp_if (Cexp_fst execution)
      (candle_cv_q_packed_object_nonpoly_run center_boxes outer_boxes radii
        sources
        (candle_cv_q_packed_object_nonpoly_step
          center_boxes outer_boxes radii source
          (Cexp_snd (Cexp_snd execution))
          (Cexp_fst (Cexp_snd execution))))
      execution)`;;

let candle_cv_q_packed_object_nonpoly_run_correct = prove
 (`!sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_nonpoly_program_run
       radii sources certificates stack result certificate_rest
     ==>
     candle_cv_q_packed_object_nonpoly_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode stack)
         (candle_cv_q_interval_list certificates)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode result)
       (candle_cv_q_interval_list certificate_rest)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_nonpoly_program_run_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_nonpoly_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_source_nonpoly_program_run_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
            (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
              (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
                (REPEAT_TCL CHOOSE_THEN
                  (CONJUNCTS_THEN2 (LABEL_TAC "step")
                    (LABEL_TAC "tail_run")))))))) THEN
    SUBGOAL_THEN
     `candle_q_packed_object_source_stack_analytic_invariant
        center_boxes outer_boxes next`
    (LABEL_TAC "next_invariant") THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_nonpoly_step_analytic_invariant THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC `h:candle_analytic_instruction` THEN
      EXISTS_TAC
        `certificates:(((num#num)#num)#((num#num)#num))list` THEN
      EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
      EXISTS_TAC
        `next_certificates:(((num#num)#num)#((num#num)#num))list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_cv_q_packed_object_nonpoly_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction h)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode stack) =
      candle_cv_q_packed_object_certificate_state T
        (candle_cv_q_packed_object_stack_encode next)
        (candle_cv_q_interval_list next_certificates)`
    (LABEL_TAC "step_compute") THENL
     [MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_step_correct THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_nonpoly_run_def;
       candle_cv_q_packed_object_certificate_state_def;
       candle_cv_bool_def; candle_cv_cval_one_suc;
       cexp_fst_def; cexp_snd_def; cexp_if_def] THEN
    USE_THEN "step_compute"
      (fun theorem ->
        REWRITE_TAC
          [REWRITE_RULE[candle_cv_q_packed_object_certificate_state_def]
            theorem]) THEN
    REWRITE_TAC[candle_cv_bool_def] THEN
    USE_THEN "induction_hypothesis"
      (fun theorem ->
        MATCH_MP_TAC
          (REWRITE_RULE
            [candle_cv_q_packed_object_certificate_state_def;
             candle_cv_bool_def]
            theorem)) THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_NONPOLY_STAGE program_run";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_certificate_from_execution_correct;
     candle_cv_q_packed_object_atn_denominator_correct;
     candle_cv_q_packed_object_nonpoly_neg_correct;
     candle_cv_q_packed_object_nonpoly_add_correct;
     candle_cv_q_packed_object_nonpoly_mul_correct;
     candle_cv_q_packed_object_nonpoly_square_correct;
     candle_cv_q_packed_object_nonpoly_pi_half_correct;
     candle_cv_q_packed_object_nonpoly_inverse_correct;
     candle_cv_q_packed_object_nonpoly_sqrt_correct;
     candle_cv_q_packed_object_nonpoly_atn_correct;
     candle_cv_q_packed_object_nonpoly_step_correct;
     candle_cv_q_packed_object_nonpoly_run_correct] then
  failwith "packed object nonpoly compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_NONPOLY_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
