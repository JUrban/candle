(* ========================================================================== *)
(* Certified acceptance for reflected signed fixed-scale polynomial models. *)
(*                                                                            *)
(* The hot evaluator keeps every intermediate Taylor-model component in the  *)
(* fixed-scale signed-integer representation.  This boundary exposes only a  *)
(* Boolean verdict and the final rational upper endpoint.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

module Candle_cv_analytic_expr_fixed_scale_accept = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;

let candle_fs_poly_result_def = new_definition
 `candle_fs_poly_result e boxes =
    candle_fs_poly_program_fixed
      (candle_fs_interval_list_of_q
        (candle_q_center_environment_list boxes))
      (candle_fs_list_of_q
        (candle_q_fixed_list_round_upper
          (candle_q_radius_list boxes)))
      (candle_poly_compile e)`;;

let candle_fs_poly_upper_def = new_definition
 `candle_fs_poly_upper e boxes =
    candle_fs_to_q
      (SND
        (candle_fs_result_value_bound
          (candle_fs_poly_result e boxes)))`;;

let candle_fs_poly_numerical_accept_def = new_definition
 `candle_fs_poly_numerical_accept e boxes <=>
    candle_fs_result_domain (candle_fs_poly_result e boxes) /\
    candle_q_box_valid_list boxes /\
    ~(candle_q_le candle_q_zero (candle_fs_poly_upper e boxes))`;;

let candle_cv_fs_poly_check_def = new_definition
 `candle_cv_fs_poly_check program boxes =
    let result =
      candle_cv_fs_poly_program_fixed
        (candle_cv_fs_interval_list_of_q
          (candle_cv_q_center_environment_list boxes))
        (candle_cv_fs_list_of_q
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes)))
        program in
    candle_cv_q_dim_whole_box_finish
      (candle_cv_fs_result_domain result)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_fs_to_q
        (Cexp_snd (candle_cv_fs_result_value_bound result)))`;;

let candle_cv_fs_poly_compute_eqs =
  union candle_cv_fs_compute_eqs
    (map SPEC_ALL [candle_cv_fs_poly_check_def]);;

let candle_cv_fs_poly_check_correct = prove
 (`!e boxes.
     candle_cv_fs_poly_check
       (candle_cv_q_instruction_list (candle_poly_compile e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_fs_poly_numerical_accept e boxes
          then SUC 0 else 0))
       (candle_cv_q (candle_fs_poly_upper e boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_check_def; LET_DEF; LET_END_DEF;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_fixed_list_round_upper_correct;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_poly_program_fixed_correct;
              candle_cv_fs_result_domain_correct;
              candle_cv_bool_def;
              candle_cv_q_box_valid_list_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fs_interval_snd_correct;
              candle_cv_fs_to_q_correct;
              candle_fs_poly_result_def;
              candle_fs_poly_upper_def;
              candle_fs_poly_numerical_accept_def;
              candle_cv_q_dim_whole_box_finish_correct]);;

let candle_fs_poly_upper_sound = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fs_result_domain (candle_fs_poly_result e boxes)
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_poly_denote_dim e p <=
       candle_q_real (candle_fs_poly_upper e boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_result_poly_invariant (type_witness:real^N) boxes
      (candle_fs_poly_result e boxes) e`
   (LABEL_TAC "invariant") THENL
   [REWRITE_TAC[candle_fs_poly_result_def] THEN
    MATCH_MP_TAC candle_fs_poly_compile_poly_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  MP_TAC
   (MATCH_MP
     (ISPECL
       [`e:candle_poly_expr`;
        `boxes:(((num#num)#num)#((num#num)#num))list`;
        `candle_fs_poly_result e boxes`;
        `type_witness:real^N`; `p:real^N`]
       candle_fs_result_poly_proxy_value_contains)
     (end_itlist CONJ
       [ASSUME
         `candle_fs_result_poly_invariant (type_witness:real^N) boxes
            (candle_fs_poly_result e boxes) e`;
        ASSUME
         `candle_fs_result_domain (candle_fs_poly_result e boxes)`;
        ASSUME
         `(p:real^N) IN interval
           [candle_q_box_lower_vector boxes,
            candle_q_box_upper_vector boxes]`])) THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_poly_upper_def; candle_fs_to_q_real] THEN
  MESON_TAC[]);;

let candle_fs_poly_numerical_accept_sound = prove
 (`!e boxes.
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_fs_poly_numerical_accept e boxes
     ==>
     !(p:real^N). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==> candle_poly_denote_dim e p < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_poly_numerical_accept_def] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  let upper_th =
    MATCH_MP
      (ISPECL
        [`e:candle_poly_expr`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `ARB:real^N`]
        candle_fs_poly_upper_sound)
      (end_itlist CONJ
        [ASSUME `candle_poly_valid_dim (dimindex (:N)) e`;
         ASSUME
          `LENGTH
            (boxes:(((num#num)#num)#((num#num)#num))list) =
           dimindex (:N)`;
         ASSUME `candle_q_box_valid_list boxes`;
         ASSUME
          `candle_fs_result_domain (candle_fs_poly_result e boxes)`]) in
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
            (candle_fs_poly_upper e boxes))`) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_poly_denote_dim e (p:real^N)`;
         `candle_q_real (candle_fs_poly_upper e boxes)`; `&0`]
        REAL_LET_TRANS)
      (CONJ upper_at_p upper_negative)));;

(* A batch keeps one source polynomial fixed and checks many exact boxes with *)
(* one evaluator entry.  The reflected checker returns only one Boolean      *)
(* verdict; the following ordinary definitions and theorems recover the      *)
(* semantic fact for every member box without trusting the batch encoder.    *)

let candle_fs_poly_batch_numerical_accept_def = define
 `(candle_fs_poly_batch_numerical_accept e [] <=> T) /\
  (candle_fs_poly_batch_numerical_accept e (CONS boxes batch) <=>
     candle_fs_poly_numerical_accept e boxes /\
     candle_fs_poly_batch_numerical_accept e batch)`;;

let candle_fs_poly_batch_numerical_accept_mem = prove
 (`!batch e boxes.
     candle_fs_poly_batch_numerical_accept e batch /\
     MEM boxes batch
     ==> candle_fs_poly_numerical_accept e boxes`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_fs_poly_batch_numerical_accept_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let candle_fs_poly_batch_covers_def = new_definition
 `candle_fs_poly_batch_covers
      (type_witness:real^N) root_boxes batch <=>
    !(p:real^N).
      p IN interval
        [candle_q_box_lower_vector root_boxes,
         candle_q_box_upper_vector root_boxes]
      ==> ?boxes. MEM boxes batch /\
            p IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`;;

let candle_fs_poly_batch_sound = prove
 (`!e root_boxes batch (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     candle_fs_poly_batch_numerical_accept e batch /\
     (!boxes. MEM boxes batch ==> LENGTH boxes = dimindex (:N)) /\
     candle_fs_poly_batch_covers type_witness root_boxes batch
     ==> !(p:real^N).
       p IN interval
         [candle_q_box_lower_vector root_boxes,
          candle_q_box_upper_vector root_boxes]
       ==> candle_poly_denote_dim e p < &0`,
  REWRITE_TAC[candle_fs_poly_batch_covers_def] THEN
  MESON_TAC[candle_fs_poly_batch_numerical_accept_mem;
            candle_fs_poly_numerical_accept_sound]);;

let candle_cv_fs_poly_batch_boxes_def = define
 `(candle_cv_fs_poly_batch_boxes [] = Cexp_num 0) /\
  (candle_cv_fs_poly_batch_boxes (CONS boxes batch) =
     Cexp_pair
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_poly_batch_boxes batch))`;;

let candle_cv_fs_poly_batch_check_def = define
 `(candle_cv_fs_poly_batch_check program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fs_poly_batch_check program (Cexp_pair boxes batch) =
     Cexp_if
       (Cexp_fst (candle_cv_fs_poly_check program boxes))
       (candle_cv_fs_poly_batch_check program batch)
       (Cexp_num 0))`;;

let candle_cv_fs_poly_batch_check_compute = prove
 (`!program batch.
     candle_cv_fs_poly_batch_check program batch =
     Cexp_if (Cexp_ispair batch)
       (Cexp_if
         (Cexp_fst
           (candle_cv_fs_poly_check program (Cexp_fst batch)))
         (candle_cv_fs_poly_batch_check program (Cexp_snd batch))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `batch:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_batch_check_def;
              cexp_if_def; cexp_fst_def; cexp_snd_def;
              cexp_ispair_def]);;

let candle_cv_fs_poly_batch_bool_and = prove
 (`!p q.
     Cexp_if (Cexp_num (if p then SUC 0 else 0))
       (Cexp_num (if q then SUC 0 else 0)) (Cexp_num 0) =
     Cexp_num (if p /\ q then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_fs_poly_batch_check_correct = prove
 (`!batch e.
     candle_cv_fs_poly_batch_check
       (candle_cv_q_instruction_list (candle_poly_compile e))
       (candle_cv_fs_poly_batch_boxes batch) =
     Cexp_num
       (if candle_fs_poly_batch_numerical_accept e batch
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_poly_batch_boxes_def;
                  candle_cv_fs_poly_batch_check_def;
                  candle_fs_poly_batch_numerical_accept_def;
                  cexp_fst_def; cexp_snd_def;
                  candle_cv_fs_poly_check_correct] THEN
  REWRITE_TAC[ONE; candle_cv_fs_poly_batch_bool_and; CONJ_ASSOC]);;

let candle_cv_fs_poly_batch_compute_eqs =
  union candle_cv_fs_poly_compute_eqs
    [SPEC_ALL candle_cv_fs_poly_batch_check_compute];;

end;;
