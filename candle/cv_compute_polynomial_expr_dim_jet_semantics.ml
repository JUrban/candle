(* ========================================================================== *)
(* Semantic bridge for normalized dimension-generic interval jets.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable jet evaluator normalizes exact *)
(* rational endpoints after addition and multiplication.  This layer proves  *)
(* that normalization preserves interval meaning, defines the corresponding  *)
(* source evaluator, and connects compiled source programs to that evaluator. *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_representation.ml";;

module Candle_cv_polynomial_expr_dim_jet_semantics = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_polynomial_expr_dim_jet_representation;;

(* Normalization is representation-only: both real endpoints are unchanged. *)

let candle_q_interval_normalize_contains = prove
 (`!i x.
     candle_q_interval_contains (candle_q_interval_normalize i) x <=>
     candle_q_interval_contains i x`,
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_normalize_def;
              candle_q_real_normalize; FST; SND]);;

let candle_q_interval_add_normalized_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains
           (candle_q_interval_add_normalized i j) (x + y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_add_normalized_def;
              candle_q_interval_normalize_contains] THEN
  MATCH_ACCEPT_TAC candle_q_interval_add_sound);;

let candle_q_interval_mul_normalized_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains
           (candle_q_interval_mul_normalized i j) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_mul_normalized_def;
              candle_q_interval_normalize_contains] THEN
  MATCH_ACCEPT_TAC candle_q_interval_mul_sound);;

(* The source evaluator mirrors the normalized executable operations while   *)
(* retaining the authenticated polynomial expression as its input.           *)

let candle_q_dim_poly_jet_normalized_def = define
 `(candle_q_dim_poly_jet_normalized boxes (Candle_poly_const p n d) =
     candle_q_dim_jet_normalized_constant boxes ((p,n),d)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_var i) =
     candle_q_dim_jet_normalized_variable boxes i) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_neg a) =
     candle_q_dim_jet_normalized_neg
       (candle_q_dim_poly_jet_normalized boxes a)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_add a b) =
     candle_q_dim_jet_normalized_add
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes b)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_mul a b) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes b)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_square a) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes a))`;;

let candle_q_dim_jet_normalized_run_append = prove
 (`!left right boxes stack.
     candle_q_dim_jet_normalized_run boxes (APPEND left right) stack =
     candle_q_dim_jet_normalized_run boxes right
       (candle_q_dim_jet_normalized_run boxes left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_q_dim_jet_normalized_run_def]);;

let candle_q_dim_poly_compile_normalized_jet_run = prove
 (`!e boxes stack.
     candle_q_dim_jet_normalized_run boxes (candle_poly_compile e) stack =
     CONS (candle_q_dim_poly_jet_normalized boxes e) stack`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_compile_def;
                  candle_q_dim_poly_jet_normalized_def;
                  candle_q_dim_jet_normalized_run_append;
                  candle_q_dim_jet_normalized_run_def;
                  candle_q_dim_jet_normalized_step_def;
                  candle_q_dim_jet_normalized_head_def;
                  candle_q_dim_jet_normalized_tail_def; APPEND]);;

let candle_q_dim_poly_compile_normalized_jet_program = prove
 (`!e boxes.
     candle_q_dim_jet_normalized_program boxes (candle_poly_compile e) =
     candle_q_dim_poly_jet_normalized boxes e`,
  REWRITE_TAC[candle_q_dim_jet_normalized_program_def;
              candle_q_dim_poly_compile_normalized_jet_run;
              candle_q_dim_jet_normalized_head_def]);;

let candle_cv_q_dim_poly_compile_program_correct = prove
 (`!e boxes.
     candle_cv_q_dim_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list (candle_poly_compile e)) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REWRITE_TAC[candle_cv_q_dim_jet_program_correct;
              candle_q_dim_poly_compile_normalized_jet_program]);;

end;;
