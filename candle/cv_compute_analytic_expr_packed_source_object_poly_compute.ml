(* ========================================================================== *)
(* Fail-closed executable replay of exact object-q polynomial instructions.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Each step returns an explicit success bit    *)
(* and encoded state stack.  Malformed instructions, out-of-range variables, *)
(* and stack underflow all return failure.                                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_item_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_poly_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_poly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_algebraic_compute;;
open Candle_cv_analytic_expr_packed_source_object_linear_compute;;
open Candle_cv_analytic_expr_packed_source_object_mul_compute;;
open Candle_cv_analytic_expr_packed_source_object_item_compute;;

let candle_cv_q_packed_object_execution_state_def = new_definition
 `candle_cv_q_packed_object_execution_state success stack =
    Cexp_pair (candle_cv_bool success) stack`;;

let candle_cv_q_packed_object_execution_failure_def = new_definition
 `candle_cv_q_packed_object_execution_failure stack =
    candle_cv_q_packed_object_execution_state F stack`;;

let candle_cv_q_packed_object_poly_step_def = new_definition
 `candle_cv_q_packed_object_poly_step center_boxes outer_boxes radii
      instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (candle_cv_q_packed_object_execution_state T
          (Cexp_pair
            (candle_cv_q_packed_object_constant_state
              (Cexp_snd instruction)) stack))
        (Cexp_if
          (candle_cv_bool_and
            (Cexp_eq (Cexp_fst instruction) (Cexp_num 1))
            (Cexp_less (Cexp_snd instruction) (Cexp_num 6)))
          (candle_cv_q_packed_object_execution_state T
            (Cexp_pair
              (candle_cv_q_packed_object_variable_state
                center_boxes outer_boxes (Cexp_snd instruction)) stack))
          (candle_cv_q_packed_object_execution_failure stack)))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_if (Cexp_ispair stack)
          (candle_cv_q_packed_object_execution_state T
            (Cexp_pair
              (candle_cv_q_packed_object_state_neg radii (Cexp_fst stack))
              (Cexp_snd stack)))
          (candle_cv_q_packed_object_execution_failure stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_if (Cexp_ispair stack)
            (Cexp_if (Cexp_ispair (Cexp_snd stack))
              (candle_cv_q_packed_object_execution_state T
                (Cexp_pair
                  (candle_cv_q_packed_object_state_add radii
                    (Cexp_fst (Cexp_snd stack)) (Cexp_fst stack))
                  (Cexp_snd (Cexp_snd stack))))
              (candle_cv_q_packed_object_execution_failure stack))
            (candle_cv_q_packed_object_execution_failure stack))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_if (Cexp_ispair stack)
              (Cexp_if (Cexp_ispair (Cexp_snd stack))
                (candle_cv_q_packed_object_execution_state T
                  (Cexp_pair
                    (candle_cv_q_packed_object_state_mul radii
                      (Cexp_fst (Cexp_snd stack)) (Cexp_fst stack))
                    (Cexp_snd (Cexp_snd stack))))
                (candle_cv_q_packed_object_execution_failure stack))
              (candle_cv_q_packed_object_execution_failure stack))
            (Cexp_if (Cexp_eq instruction (Cexp_num 5))
              (Cexp_if (Cexp_ispair stack)
                (candle_cv_q_packed_object_execution_state T
                  (Cexp_pair
                    (candle_cv_q_packed_object_state_mul radii
                      (Cexp_fst stack) (Cexp_fst stack))
                    (Cexp_snd stack)))
                (candle_cv_q_packed_object_execution_failure stack))
              (candle_cv_q_packed_object_execution_failure stack)))))`;;

let candle_cv_q_packed_object_poly_step_push_correct = prove
 (`!center_boxes outer_boxes radii positive negative denominator_predecessor
       stack.
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction
         (Candle_q_push positive negative denominator_predecessor))
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (Candle_q_packed_object_item
             (Candle_q_packed_object_state T
               (candle_q_packed_object_constant_interval
                 positive negative denominator_predecessor)
               candle_q_packed_object_zero_gradient6
               (candle_q_packed_object_constant_interval
                 positive negative denominator_predecessor)
               candle_q_packed_object_zero_gradient6
               candle_q_packed_object_zero_hessian21)
             (Candle_analytic_poly
               (Candle_poly_const
                 positive negative denominator_predecessor))
             (Candle_analytic_poly
               (Candle_poly_const
                 positive negative denominator_predecessor)))
           stack))`,
  REWRITE_TAC
    [candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_instruction_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def;
     cexp_eq_def; cexp_if_def;
     candle_cv_q_packed_object_constant_state_correct;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE push";;

let candle_cv_q_packed_object_poly_step_load_correct = prove
 (`!center_boxes outer_boxes radii variable stack.
     variable < 6
     ==>
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction (Candle_q_load variable))
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (Candle_q_packed_object_item
             (Candle_q_packed_object_state T
               (candle_q_interval_lookup variable center_boxes)
               (candle_q_packed_object_unit_gradient6 variable)
               (candle_q_interval_lookup variable outer_boxes)
               (candle_q_packed_object_unit_gradient6 variable)
               candle_q_packed_object_zero_hessian21)
             (Candle_analytic_poly (Candle_poly_var variable))
             (Candle_analytic_poly (Candle_poly_var variable)))
           stack))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_instruction_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def;
     cexp_eq_def; cexp_less_def; cexp_if_def;
     injectivity "cval"; injectivity "num"; NOT_SUC;
     candle_cv_bool_and_def;
     candle_cv_q_packed_object_variable_state_correct;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE load";;

let candle_cv_q_packed_object_poly_step_neg_correct = prove
 (`!center_boxes outer_boxes radii item rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction Candle_q_neg)
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS (candle_q_packed_object_source_item_neg radii item) rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_neg
      (candle_cv_q_list radii)
      (candle_cv_q_packed_object_item_state_encode item) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_neg radii item)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `item:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_neg_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_poly_step_def;
       candle_cv_q_instruction_def;
       candle_cv_q_packed_object_stack_encode_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC] THEN
    ASM_REWRITE_TAC[cexp_if_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE neg";;

let candle_cv_q_packed_object_poly_step_add_correct = prove
 (`!center_boxes outer_boxes radii left right rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction Candle_q_add)
       (candle_cv_q_packed_object_stack_encode
         (CONS right (CONS left rest))) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_add radii left right)
           rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_add
      (candle_cv_q_list radii)
      (candle_cv_q_packed_object_item_state_encode left)
      (candle_cv_q_packed_object_item_state_encode right) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_add radii left right)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `left:candle_q_packed_object_item`;
         `right:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_add_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_poly_step_def;
       candle_cv_q_instruction_def;
       candle_cv_q_packed_object_stack_encode_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC] THEN
    ASM_REWRITE_TAC[cexp_if_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE add";;

let candle_cv_q_packed_object_poly_step_mul_correct = prove
 (`!center_boxes outer_boxes radii left right rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction Candle_q_mul)
       (candle_cv_q_packed_object_stack_encode
         (CONS right (CONS left rest))) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_mul radii left right)
           rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_mul
      (candle_cv_q_list radii)
      (candle_cv_q_packed_object_item_state_encode left)
      (candle_cv_q_packed_object_item_state_encode right) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_mul radii left right)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `left:candle_q_packed_object_item`;
         `right:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_mul_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_poly_step_def;
       candle_cv_q_instruction_def;
       candle_cv_q_packed_object_stack_encode_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC] THEN
    ASM_REWRITE_TAC[cexp_if_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE mul";;

let candle_cv_q_packed_object_poly_step_square_correct = prove
 (`!center_boxes outer_boxes radii item rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_poly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction Candle_q_square)
       (candle_cv_q_packed_object_stack_encode (CONS item rest)) =
     candle_cv_q_packed_object_execution_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_source_item_mul radii item item)
           rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_state_mul
      (candle_cv_q_list radii)
      (candle_cv_q_packed_object_item_state_encode item)
      (candle_cv_q_packed_object_item_state_encode item) =
    candle_cv_q_packed_object_item_state_encode
      (candle_q_packed_object_source_item_mul radii item item)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `item:candle_q_packed_object_item`;
         `item:candle_q_packed_object_item`]
        candle_cv_q_packed_object_source_item_mul_correct) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
      [candle_cv_q_packed_object_poly_step_def;
       candle_cv_q_instruction_def;
       candle_cv_q_packed_object_stack_encode_def;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC] THEN
    ASM_REWRITE_TAC[cexp_if_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_POLY_STAGE square";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_poly_step_push_correct;
     candle_cv_q_packed_object_poly_step_load_correct;
     candle_cv_q_packed_object_poly_step_neg_correct;
     candle_cv_q_packed_object_poly_step_add_correct;
     candle_cv_q_packed_object_poly_step_mul_correct;
     candle_cv_q_packed_object_poly_step_square_correct] then
  failwith "packed object poly compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_POLY_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
