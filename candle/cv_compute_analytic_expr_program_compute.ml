(* ========================================================================== *)
(* cval execution for compiled nested reflected analytic expressions.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable stack carries a domain bit and *)
(* a complete interval jet.  Malformed instructions produce a failed result; *)
(* represented well-typed programs are proved equal to their ordinary HOL    *)
(* specification below.                                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_program.ml";;

module Candle_cv_analytic_expr_program_compute = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;

let candle_cv_bool_def = new_definition
 `candle_cv_bool b = Cexp_num (if b then SUC 0 else 0)`;;

let candle_cv_bool_and_def = new_definition
 `candle_cv_bool_and a b = Cexp_if a b (Cexp_num 0)`;;

let candle_cv_q_dim_analytic_result_make_def = new_definition
 `candle_cv_q_dim_analytic_result_make domain jet =
    Cexp_pair domain jet`;;

let candle_cv_q_dim_analytic_result_domain_def = new_definition
 `candle_cv_q_dim_analytic_result_domain result = Cexp_fst result`;;

let candle_cv_q_dim_analytic_result_jet_def = new_definition
 `candle_cv_q_dim_analytic_result_jet result = Cexp_snd result`;;

let candle_cv_q_dim_analytic_result_default_def = new_definition
 `candle_cv_q_dim_analytic_result_default boxes =
    candle_cv_q_dim_analytic_result_make (Cexp_num 0)
      (candle_cv_q_dim_jet_zero boxes)`;;

let candle_cv_q_dim_analytic_result_head_def = new_definition
 `candle_cv_q_dim_analytic_result_head boxes stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_q_dim_analytic_result_default boxes)`;;

let candle_cv_q_dim_analytic_result_tail_def = new_definition
 `candle_cv_q_dim_analytic_result_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_q_dim_analytic_result_neg_def = new_definition
 `candle_cv_q_dim_analytic_result_neg result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_q_dim_analytic_result_domain result)
      (candle_cv_q_dim_jet_neg
        (candle_cv_q_dim_analytic_result_jet result))`;;

let candle_cv_q_dim_analytic_result_add_def = new_definition
 `candle_cv_q_dim_analytic_result_add left right =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain left)
        (candle_cv_q_dim_analytic_result_domain right))
      (candle_cv_q_dim_jet_add
        (candle_cv_q_dim_analytic_result_jet left)
        (candle_cv_q_dim_analytic_result_jet right))`;;

let candle_cv_q_dim_analytic_result_mul_def = new_definition
 `candle_cv_q_dim_analytic_result_mul left right =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain left)
        (candle_cv_q_dim_analytic_result_domain right))
      (candle_cv_q_dim_jet_mul
        (candle_cv_q_dim_analytic_result_jet left)
        (candle_cv_q_dim_analytic_result_jet right))`;;

let candle_cv_q_dim_analytic_result_square_def = new_definition
 `candle_cv_q_dim_analytic_result_square result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_q_dim_analytic_result_domain result)
      (candle_cv_q_dim_jet_mul
        (candle_cv_q_dim_analytic_result_jet result)
        (candle_cv_q_dim_analytic_result_jet result))`;;

let candle_cv_q_dim_analytic_result_inv_def = new_definition
 `candle_cv_q_dim_analytic_result_inv result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain result)
        (candle_cv_q_dim_jet_inv_domain
          (candle_cv_q_dim_analytic_result_jet result)))
      (candle_cv_q_dim_jet_inv
        (candle_cv_q_dim_analytic_result_jet result))`;;

let candle_cv_q_dim_analytic_result_sqrt_def = new_definition
 `candle_cv_q_dim_analytic_result_sqrt s result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain result)
        (candle_cv_q_dim_jet_sqrt_domain s
          (candle_cv_q_dim_analytic_result_jet result)))
      (candle_cv_q_dim_jet_sqrt_with s
        (candle_cv_q_dim_analytic_result_jet result))`;;

let candle_cv_q_dim_analytic_result_atn_def = new_definition
 `candle_cv_q_dim_analytic_result_atn result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain result)
        (candle_cv_q_dim_jet_atn_domain
          (candle_cv_q_dim_analytic_result_jet result)))
      (candle_cv_q_dim_jet_atn
        (candle_cv_q_dim_analytic_result_jet result))`;;

let candle_cv_q_dim_analytic_result_pi_half_def = new_definition
 `candle_cv_q_dim_analytic_result_pi_half boxes =
    candle_cv_q_dim_analytic_result_make (Cexp_num 1)
      (candle_cv_q_dim_jet_pi_half boxes)`;;

let candle_cv_analytic_instruction_def = define
 `(candle_cv_analytic_instruction
     (Candle_analytic_push_poly program) =
     Cexp_pair (Cexp_num 0) (candle_cv_q_instruction_list program)) /\
  (candle_cv_analytic_instruction Candle_analytic_program_neg =
     Cexp_num 2) /\
  (candle_cv_analytic_instruction Candle_analytic_program_add =
     Cexp_num 3) /\
  (candle_cv_analytic_instruction Candle_analytic_program_mul =
     Cexp_num 4) /\
  (candle_cv_analytic_instruction Candle_analytic_program_square =
     Cexp_num 5) /\
  (candle_cv_analytic_instruction Candle_analytic_program_inv =
     Cexp_num 6) /\
  (candle_cv_analytic_instruction (Candle_analytic_program_sqrt s) =
     Cexp_pair (Cexp_num 1) (candle_cv_q_interval s)) /\
  (candle_cv_analytic_instruction Candle_analytic_program_atn =
     Cexp_num 7) /\
  (candle_cv_analytic_instruction Candle_analytic_program_pi_half =
     Cexp_num 8)`;;

let candle_cv_analytic_instruction_list_def = define
 `(candle_cv_analytic_instruction_list [] = Cexp_num 0) /\
  (candle_cv_analytic_instruction_list (CONS h t) =
     Cexp_pair (candle_cv_analytic_instruction h)
       (candle_cv_analytic_instruction_list t))`;;

let candle_cv_q_dim_analytic_result_encode_def = new_definition
 `candle_cv_q_dim_analytic_result_encode result =
    candle_cv_q_dim_analytic_result_make
      (candle_cv_bool (FST result))
      (candle_cv_q_dim_jet_encode (SND result))`;;

let candle_cv_q_dim_analytic_result_list_encode_def = define
 `(candle_cv_q_dim_analytic_result_list_encode [] = Cexp_num 0) /\
  (candle_cv_q_dim_analytic_result_list_encode (CONS h t) =
     Cexp_pair (candle_cv_q_dim_analytic_result_encode h)
       (candle_cv_q_dim_analytic_result_list_encode t))`;;

let candle_cv_q_dim_analytic_program_step_def = new_definition
 `candle_cv_q_dim_analytic_program_step boxes instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_q_dim_analytic_result_make (Cexp_num 1)
            (candle_cv_q_dim_jet_program boxes (Cexp_snd instruction)))
          stack)
        (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 1))
          (Cexp_pair
            (candle_cv_q_dim_analytic_result_sqrt (Cexp_snd instruction)
              (candle_cv_q_dim_analytic_result_head boxes stack))
            (candle_cv_q_dim_analytic_result_tail stack))
          (Cexp_pair (candle_cv_q_dim_analytic_result_default boxes)
            stack)))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_dim_analytic_result_neg
            (candle_cv_q_dim_analytic_result_head boxes stack))
          (candle_cv_q_dim_analytic_result_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_dim_analytic_result_add
              (candle_cv_q_dim_analytic_result_head boxes
                (candle_cv_q_dim_analytic_result_tail stack))
              (candle_cv_q_dim_analytic_result_head boxes stack))
            (candle_cv_q_dim_analytic_result_tail
              (candle_cv_q_dim_analytic_result_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_q_dim_analytic_result_mul
                (candle_cv_q_dim_analytic_result_head boxes
                  (candle_cv_q_dim_analytic_result_tail stack))
                (candle_cv_q_dim_analytic_result_head boxes stack))
              (candle_cv_q_dim_analytic_result_tail
                (candle_cv_q_dim_analytic_result_tail stack)))
            (Cexp_if (Cexp_eq instruction (Cexp_num 5))
              (Cexp_pair
                (candle_cv_q_dim_analytic_result_square
                  (candle_cv_q_dim_analytic_result_head boxes stack))
                (candle_cv_q_dim_analytic_result_tail stack))
              (Cexp_if (Cexp_eq instruction (Cexp_num 6))
                (Cexp_pair
                  (candle_cv_q_dim_analytic_result_inv
                    (candle_cv_q_dim_analytic_result_head boxes stack))
                  (candle_cv_q_dim_analytic_result_tail stack))
                (Cexp_if (Cexp_eq instruction (Cexp_num 7))
                  (Cexp_pair
                    (candle_cv_q_dim_analytic_result_atn
                      (candle_cv_q_dim_analytic_result_head boxes stack))
                    (candle_cv_q_dim_analytic_result_tail stack))
                  (Cexp_if (Cexp_eq instruction (Cexp_num 8))
                    (Cexp_pair
                      (candle_cv_q_dim_analytic_result_pi_half boxes) stack)
                    (Cexp_pair
                      (candle_cv_q_dim_analytic_result_default boxes)
                      stack))))))))`;;

let candle_cv_q_dim_analytic_program_run_def = define
 `(candle_cv_q_dim_analytic_program_run boxes (Cexp_num n) stack = stack) /\
  (candle_cv_q_dim_analytic_program_run boxes (Cexp_pair h t) stack =
     candle_cv_q_dim_analytic_program_run boxes t
       (candle_cv_q_dim_analytic_program_step boxes h stack))`;;

let candle_cv_q_dim_analytic_program_run_compute = prove
 (`!boxes program stack.
     candle_cv_q_dim_analytic_program_run boxes program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_dim_analytic_program_run boxes (Cexp_snd program)
         (candle_cv_q_dim_analytic_program_step boxes
           (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_program_run_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_analytic_program_def = new_definition
 `candle_cv_q_dim_analytic_program boxes program =
    candle_cv_q_dim_analytic_result_head boxes
      (candle_cv_q_dim_analytic_program_run boxes program (Cexp_num 0))`;;


let candle_cv_bool_and_correct = prove
 (`!a b.
     candle_cv_bool_and (candle_cv_bool a) (candle_cv_bool b) =
     candle_cv_bool (a /\ b)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[candle_cv_bool_and_def; candle_cv_bool_def;
              cexp_if_def]);;
let candle_cv_q_dim_analytic_result_make_correct = prove
 (`!domain jet.
     candle_cv_q_dim_analytic_result_make
       (candle_cv_bool domain) (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_dim_analytic_result_encode (domain,jet)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_make_def;
              candle_cv_q_dim_analytic_result_encode_def; FST; SND]);;
let candle_cv_q_dim_analytic_result_domain_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_domain
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_bool (candle_q_dim_analytic_result_domain result)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_domain_def;
              candle_cv_q_dim_analytic_result_encode_def;
              candle_cv_q_dim_analytic_result_make_def;
              candle_q_dim_analytic_result_domain_def;
              cexp_fst_def; FST]);;
let candle_cv_q_dim_analytic_result_jet_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_jet
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_analytic_result_jet result)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_jet_def;
              candle_cv_q_dim_analytic_result_encode_def;
              candle_cv_q_dim_analytic_result_make_def;
              candle_q_dim_analytic_result_jet_def;
              cexp_snd_def; SND]);;
let candle_cv_q_dim_analytic_result_default_correct = prove
 (`!boxes.
     candle_cv_q_dim_analytic_result_default
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_result_default boxes)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_default_def;
              candle_q_dim_analytic_result_default_def;
              candle_cv_q_dim_jet_zero_correct;
              candle_cv_q_dim_analytic_result_encode_def;
              candle_cv_q_dim_analytic_result_make_def;
              candle_cv_bool_def; ARITH_RULE `SUC 0 = 1`; FST; SND]);;
let candle_cv_q_dim_analytic_result_head_correct = prove
 (`!boxes stack.
     candle_cv_q_dim_analytic_result_head
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_result_list_encode stack) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_result_head boxes stack)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_result_head_def;
              candle_cv_q_dim_analytic_result_list_encode_def;
              candle_q_dim_analytic_result_head_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_q_dim_analytic_result_default_correct]);;
let candle_cv_q_dim_analytic_result_tail_correct = prove
 (`!stack.
     candle_cv_q_dim_analytic_result_tail
       (candle_cv_q_dim_analytic_result_list_encode stack) =
     candle_cv_q_dim_analytic_result_list_encode
       (candle_q_dim_analytic_result_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_result_tail_def;
              candle_cv_q_dim_analytic_result_list_encode_def;
              candle_q_dim_analytic_result_tail_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;
let candle_cv_q_dim_analytic_result_neg_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_neg
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_result_domain result,
        candle_q_dim_jet_normalized_neg
          (candle_q_dim_analytic_result_jet result))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_neg_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_dim_jet_neg_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_add_correct = prove
 (`!left right.
     candle_cv_q_dim_analytic_result_add
       (candle_cv_q_dim_analytic_result_encode left)
       (candle_cv_q_dim_analytic_result_encode right) =
     candle_cv_q_dim_analytic_result_encode
       ((candle_q_dim_analytic_result_domain left /\
         candle_q_dim_analytic_result_domain right),
        candle_q_dim_jet_normalized_add
          (candle_q_dim_analytic_result_jet left)
          (candle_q_dim_analytic_result_jet right))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_add_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_jet_add_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_mul_correct = prove
 (`!left right.
     candle_cv_q_dim_analytic_result_mul
       (candle_cv_q_dim_analytic_result_encode left)
       (candle_cv_q_dim_analytic_result_encode right) =
     candle_cv_q_dim_analytic_result_encode
       ((candle_q_dim_analytic_result_domain left /\
         candle_q_dim_analytic_result_domain right),
        candle_q_dim_jet_normalized_mul
          (candle_q_dim_analytic_result_jet left)
          (candle_q_dim_analytic_result_jet right))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_mul_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_jet_mul_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_square_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_square
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_result_domain result,
        candle_q_dim_jet_normalized_mul
          (candle_q_dim_analytic_result_jet result)
          (candle_q_dim_analytic_result_jet result))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_square_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_dim_jet_mul_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_jet_inv_domain_bool_correct = prove
 (`!jet.
     candle_cv_q_dim_jet_inv_domain (candle_cv_q_dim_jet_encode jet) =
     candle_cv_bool (candle_q_dim_jet_inv_domain jet)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_inv_domain_correct;
              candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_dim_jet_sqrt_domain_bool_correct = prove
 (`!s jet.
     candle_cv_q_dim_jet_sqrt_domain
       (candle_cv_q_interval s) (candle_cv_q_dim_jet_encode jet) =
     candle_cv_bool (candle_q_dim_jet_sqrt_domain s jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_domain_correct;
              candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_dim_jet_atn_domain_bool_correct = prove
 (`!jet.
     candle_cv_q_dim_jet_atn_domain (candle_cv_q_dim_jet_encode jet) =
     candle_cv_bool (candle_q_dim_jet_atn_domain jet)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_domain_correct;
              candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_dim_analytic_result_inv_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_inv
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_analytic_result_encode
       ((candle_q_dim_analytic_result_domain result /\
         candle_q_dim_jet_inv_domain
           (candle_q_dim_analytic_result_jet result)),
        candle_q_dim_jet_inv
          (candle_q_dim_analytic_result_jet result))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_inv_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_dim_jet_inv_domain_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_jet_inv_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_sqrt_correct = prove
 (`!s result.
     candle_cv_q_dim_analytic_result_sqrt
       (candle_cv_q_interval s)
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_analytic_result_encode
       ((candle_q_dim_analytic_result_domain result /\
         candle_q_dim_jet_sqrt_domain s
           (candle_q_dim_analytic_result_jet result)),
        candle_q_dim_jet_sqrt_with s
          (candle_q_dim_analytic_result_jet result))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_sqrt_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_dim_jet_sqrt_domain_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_jet_sqrt_with_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_atn_correct = prove
 (`!result.
     candle_cv_q_dim_analytic_result_atn
       (candle_cv_q_dim_analytic_result_encode result) =
     candle_cv_q_dim_analytic_result_encode
       ((candle_q_dim_analytic_result_domain result /\
         candle_q_dim_jet_atn_domain
           (candle_q_dim_analytic_result_jet result)),
        candle_q_dim_jet_atn
          (candle_q_dim_analytic_result_jet result))`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_atn_def;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_dim_jet_atn_domain_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_jet_atn_correct;
              candle_cv_q_dim_analytic_result_make_correct]);;
let candle_cv_q_dim_analytic_result_pi_half_correct = prove
 (`!boxes.
     candle_cv_q_dim_analytic_result_pi_half
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_analytic_result_encode
       (T,candle_q_dim_jet_pi_half boxes)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_result_pi_half_def;
              candle_cv_q_dim_jet_pi_half_correct;
              candle_cv_q_dim_analytic_result_encode_def;
              candle_cv_q_dim_analytic_result_make_def;
              candle_cv_bool_def; ARITH_RULE `SUC 0 = 1`; FST; SND]);;
let candle_six_ne_two = EQT_ELIM (NUM_REDUCE_CONV `~(6 = 2)`);;
let candle_six_ne_three = EQT_ELIM (NUM_REDUCE_CONV `~(6 = 3)`);;
let candle_six_ne_four = EQT_ELIM (NUM_REDUCE_CONV `~(6 = 4)`);;
let candle_six_ne_five = EQT_ELIM (NUM_REDUCE_CONV `~(6 = 5)`);;
let candle_seven_ne_two = EQT_ELIM (NUM_REDUCE_CONV `~(7 = 2)`);;
let candle_seven_ne_three = EQT_ELIM (NUM_REDUCE_CONV `~(7 = 3)`);;
let candle_seven_ne_four = EQT_ELIM (NUM_REDUCE_CONV `~(7 = 4)`);;
let candle_seven_ne_five = EQT_ELIM (NUM_REDUCE_CONV `~(7 = 5)`);;
let candle_seven_ne_six = EQT_ELIM (NUM_REDUCE_CONV `~(7 = 6)`);;
let candle_eight_ne_two = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 2)`);;
let candle_eight_ne_three = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 3)`);;
let candle_eight_ne_four = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 4)`);;
let candle_eight_ne_five = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 5)`);;
let candle_eight_ne_six = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 6)`);;
let candle_eight_ne_seven = EQT_ELIM (NUM_REDUCE_CONV `~(8 = 7)`);;

let candle_cv_q_dim_analytic_step_correct_rewrites =
 [candle_cv_q_dim_analytic_program_step_def;
  candle_cv_analytic_instruction_def;
  candle_q_dim_analytic_program_step_def;
  candle_cv_q_dim_analytic_result_list_encode_def;
  ARITH_RULE `1 = SUC 0`;
  cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
  cexp_eq_def; distinctness "cval"; injectivity "cval";
  NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
  candle_four_ne_three; candle_three_ne_two;
  candle_five_ne_two; candle_five_ne_three;
  candle_five_ne_four; candle_six_ne_two;
  candle_six_ne_three; candle_six_ne_four;
  candle_six_ne_five;
  candle_seven_ne_two; candle_seven_ne_three;
  candle_seven_ne_four; candle_seven_ne_five;
  candle_seven_ne_six;
  candle_eight_ne_two; candle_eight_ne_three;
  candle_eight_ne_four; candle_eight_ne_five;
  candle_eight_ne_six; candle_eight_ne_seven;
  candle_cv_q_dim_analytic_result_head_correct;
  candle_cv_q_dim_analytic_result_tail_correct];;

let candle_cv_q_dim_analytic_program_step_correct = prove
 (`!instruction boxes stack.
     candle_cv_q_dim_analytic_program_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_analytic_instruction instruction)
       (candle_cv_q_dim_analytic_result_list_encode stack) =
     candle_cv_q_dim_analytic_result_list_encode
       (candle_q_dim_analytic_program_step boxes instruction stack)`,
  MATCH_MP_TAC candle_analytic_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_jet_program_correct;
       candle_cv_q_dim_analytic_result_encode_def;
       candle_cv_q_dim_analytic_result_make_def;
       candle_cv_bool_def]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_neg_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_add_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_mul_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_square_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_inv_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_sqrt_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_atn_correct]);
    REWRITE_TAC
     (candle_cv_q_dim_analytic_step_correct_rewrites @
      [candle_cv_q_dim_analytic_result_pi_half_correct])]);;
let candle_cv_q_dim_analytic_program_run_correct = prove
 (`!program boxes stack.
     candle_cv_q_dim_analytic_program_run
       (candle_cv_q_interval_list boxes)
       (candle_cv_analytic_instruction_list program)
       (candle_cv_q_dim_analytic_result_list_encode stack) =
     candle_cv_q_dim_analytic_result_list_encode
       (candle_q_dim_analytic_program_run boxes program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                  candle_cv_q_dim_analytic_program_run_def;
                  candle_q_dim_analytic_program_run_def;
                  candle_cv_q_dim_analytic_program_step_correct]);;
let candle_cv_q_dim_analytic_program_correct = prove
 (`!program boxes.
     candle_cv_q_dim_analytic_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_analytic_instruction_list program) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_program boxes program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_program_def;
              candle_q_dim_analytic_program_def;
              GSYM candle_cv_q_dim_analytic_result_list_encode_def;
              candle_cv_q_dim_analytic_program_run_correct;
              candle_cv_q_dim_analytic_result_head_correct]);;
let candle_cv_q_dim_analytic_compile_program_correct = prove
 (`!e boxes.
     candle_cv_q_dim_analytic_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile e)) =
     candle_cv_q_dim_analytic_result_encode
       (candle_q_dim_analytic_domain boxes e,
        candle_q_dim_analytic_jet boxes e)`,
  REWRITE_TAC[candle_cv_q_dim_analytic_program_correct;
              candle_q_dim_analytic_compile_program]);;
let candle_cv_q_dim_analytic_program_compute_eqs =
  candle_cv_q_dim_jet_sqrt_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_atn_zero_compute; candle_cv_q_atn_one_compute;
    candle_cv_q_atn_neg_one_compute; candle_cv_q_atn_third_compute;
    candle_cv_q_atn_fifth_compute; candle_cv_q_atn_seventh_compute;
    candle_cv_q_atn_ninth_compute; candle_cv_q_atn_eleventh_compute;
    candle_cv_q_atn_thirteenth_compute;
    candle_cv_q_atn_pos_lower_compute; candle_cv_q_atn_pos_upper_compute;
    candle_cv_q_atn_lower_def; candle_cv_q_atn_upper_def;
    candle_cv_q_interval_atn_series_def;
    candle_cv_q_interval_atn_series_domain_def;
    candle_cv_q_atn_one_interval_def;
    candle_cv_q_dim_jet_atn_denominator_def;
    candle_cv_q_dim_jet_atn_d_def;
    candle_cv_q_dim_jet_atn_dd_def;
    candle_cv_q_dim_jet_atn_with_def;
    candle_cv_q_dim_jet_atn_def;
    candle_cv_q_dim_jet_atn_domain_def;
    candle_cv_q_pi_half_interval_compute;
    candle_cv_q_dim_jet_pi_half_def] @
  map SPEC_ALL
   [candle_cv_bool_and_def;
    candle_cv_q_dim_analytic_result_make_def;
    candle_cv_q_dim_analytic_result_domain_def;
    candle_cv_q_dim_analytic_result_jet_def;
    candle_cv_q_dim_analytic_result_default_def;
    candle_cv_q_dim_analytic_result_head_def;
    candle_cv_q_dim_analytic_result_tail_def;
    candle_cv_q_dim_analytic_result_neg_def;
    candle_cv_q_dim_analytic_result_add_def;
    candle_cv_q_dim_analytic_result_mul_def;
    candle_cv_q_dim_analytic_result_square_def;
    candle_cv_q_dim_analytic_result_inv_def;
    candle_cv_q_dim_analytic_result_sqrt_def;
    candle_cv_q_dim_analytic_result_atn_def;
    candle_cv_q_dim_analytic_result_pi_half_def;
    candle_cv_q_dim_analytic_program_step_def;
    candle_cv_q_dim_analytic_program_run_compute;
    candle_cv_q_dim_analytic_program_def];;

end;;
