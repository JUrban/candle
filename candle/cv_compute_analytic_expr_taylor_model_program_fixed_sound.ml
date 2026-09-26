(* ========================================================================== *)
(* Analytic-invariant bridge for fixed-scale polynomial Taylor blocks.       *)
(*                                                                            *)
(* The fixed evaluator already proves value, gradient, and Hessian           *)
(* containment for every valid compiled polynomial.  This file identifies   *)
(* those generic partials with the analytic-expression semantics, so the     *)
(* result can be consumed by the existing universal Taylor-model invariant.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_sound = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;

let candle_poly_value_list_denote_at_dim = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     candle_poly_value_list
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     candle_poly_denote_dim e z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_def] THEN
  ASM_SIMP_TAC[candle_poly_value_list_fun]);;

let candle_poly_d_list_partial_at_dim = prove
 (`!e (z:real^N) di.
     candle_poly_valid_dim (dimindex (:N)) e /\
     di < dimindex (:N)
     ==>
     candle_poly_d_list di
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     partial (di + 1) (candle_poly_denote_dim e) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_poly_d_list_fun] THEN
  MP_TAC
    (ISPECL
      [`e:candle_poly_expr`; `z:real^N`; `di + 1`; `di + 1`]
      candle_poly_denote_dim_partials) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`] THEN MESON_TAC[]]);;

let candle_poly_dd_list_partial2_at_dim = prove
 (`!e (z:real^N) di dj.
     candle_poly_valid_dim (dimindex (:N)) e /\
     di < dimindex (:N) /\
     dj < dimindex (:N)
     ==>
     candle_poly_dd_list dj di
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     partial2 (dj + 1) (di + 1) (candle_poly_denote_dim e) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_poly_dd_list_fun] THEN
  MP_TAC
    (ISPECL
      [`e:candle_poly_expr`; `z:real^N`; `di + 1`; `dj + 1`]
      candle_poly_denote_dim_partials) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`;
                ARITH_RULE `(dj + 1) - 1 = dj`] THEN MESON_TAC[]]);;

let candle_q_dim_poly_analytic_contains_partials = prove
 (`!e jet (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     (candle_q_dim_analytic_contains (dimindex (:N)) jet
        (list_of_seq (\k. z$(k + 1)) (dimindex (:N)))
        (Candle_analytic_poly e) <=>
      candle_q_dim_jet_contains_components (dimindex (:N)) jet
        (candle_poly_denote_dim e z)
        (\di. partial (di + 1) (candle_poly_denote_dim e) z)
        (\di dj. partial2 (dj + 1) (di + 1)
          (candle_poly_denote_dim e) z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_q_dim_jet_contains_components_def] THEN
  ASM_SIMP_TAC[candle_poly_value_list_denote_at_dim;
               candle_poly_d_list_partial_at_dim;
               candle_poly_dd_list_partial2_at_dim]);;

let candle_fs_result_to_q_domain = prove
 (`!result.
     candle_q_dim_taylor_model_result_domain
       (candle_fs_result_to_q result) =
     candle_fs_result_domain result`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_fs_poly_program_to_q_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_poly_program_to_q
         (candle_q_center_environment_list boxes)
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_result_poly_invariant (type_witness:real^N) boxes
      (candle_fs_poly_program_fixed
        (candle_fs_interval_list_of_q
          (candle_q_center_environment_list boxes))
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
        (candle_poly_compile e)) e`
   (LABEL_TAC "fixed_invariant") THENL
   [MATCH_MP_TAC candle_fs_poly_compile_poly_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_poly_program_to_q_def;
              candle_fs_poly_program_def;
              candle_fs_result_to_q_domain] THEN
  DISCH_TAC THEN
  USE_THEN "fixed_invariant" MP_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
        (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
          (LABEL_TAC "proxy_contains")))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_regular_at_def];
    REWRITE_TAC[candle_analytic_regular_at_def];
    USE_THEN "center_shape" ACCEPT_TAC;
    ASM_SIMP_TAC[candle_q_dim_poly_analytic_contains_partials] THEN
    USE_THEN "center_contains" ACCEPT_TAC;
    USE_THEN "proxy_shape" ACCEPT_TAC;
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_poly_analytic_contains_partials] THEN
    USE_THEN "proxy_contains" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE poly-invariant";;

(* Only paired polynomial instructions take the fixed path.  Every other    *)
(* instruction delegates to the established rational analytic step, so all *)
(* nonlinear guards and their existing preservation theorems stay intact.  *)

let candle_q_dim_taylor_model_program_fixed_step_def = new_definition
 `candle_q_dim_taylor_model_program_fixed_step
      center_boxes boxes radii center_instruction box_instruction stack =
    if candle_q_analytic_instruction_tag center_instruction = 0 /\
       candle_q_analytic_instruction_tag box_instruction = 0
    then CONS
      (candle_fs_poly_program_to_q center_boxes radii
        (candle_q_analytic_instruction_poly center_instruction)) stack
    else candle_q_dim_taylor_model_program_step
      center_boxes boxes radii center_instruction box_instruction stack`;;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE fixed-step";;

let candle_q_dim_taylor_model_program_fixed_run_def = define
 `(candle_q_dim_taylor_model_program_fixed_run
     center_boxes boxes radii [] box_program stack = stack) /\
  (candle_q_dim_taylor_model_program_fixed_run
     center_boxes boxes radii (CONS ch ct) [] stack = stack) /\
  (candle_q_dim_taylor_model_program_fixed_run
     center_boxes boxes radii (CONS ch ct) (CONS bh bt) stack =
     candle_q_dim_taylor_model_program_fixed_run
       center_boxes boxes radii ct bt
       (candle_q_dim_taylor_model_program_fixed_step
         center_boxes boxes radii ch bh stack))`;;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE fixed-run";;

let candle_q_dim_taylor_model_program_fixed_def = new_definition
 `candle_q_dim_taylor_model_program_fixed center_program box_program boxes =
    candle_q_dim_taylor_model_result_head
      (candle_q_center_environment_list boxes) boxes
      (candle_q_dim_taylor_model_program_fixed_run
        (candle_q_center_environment_list boxes) boxes
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        center_program box_program [])`;;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE fixed-program";;

let candle_q_dim_taylor_model_program_fixed_run_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii stack.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       center_right box_right
       (candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
         center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND;
                candle_q_dim_taylor_model_program_fixed_run_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_q_dim_taylor_model_program_fixed_run_def] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE append";;

let candle_q_dim_taylor_model_program_fixed_step_poly = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       (Candle_analytic_push_poly center_program)
       (Candle_analytic_push_poly box_program) stack =
     CONS
       (candle_fs_poly_program_to_q center_boxes radii center_program) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def]);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-poly";;

let candle_q_dim_taylor_model_program_fixed_step_neg = prove
 (`!center_boxes boxes radii inner stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_neg Candle_analytic_program_neg
       (CONS inner stack) =
     CONS (candle_q_dim_taylor_model_result_neg radii inner) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_neg] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-neg";;

let candle_q_dim_taylor_model_program_fixed_step_add = prove
 (`!center_boxes boxes radii left right stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_add Candle_analytic_program_add
       (CONS right (CONS left stack)) =
     CONS (candle_q_dim_taylor_model_result_add radii left right) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_add] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-add";;

let candle_q_dim_taylor_model_program_fixed_step_mul = prove
 (`!center_boxes boxes radii left right stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_mul Candle_analytic_program_mul
       (CONS right (CONS left stack)) =
     CONS (candle_q_dim_taylor_model_result_mul radii left right) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_mul] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-mul";;

let candle_q_dim_taylor_model_program_fixed_step_square = prove
 (`!center_boxes boxes radii inner stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_square Candle_analytic_program_square
       (CONS inner stack) =
     CONS (candle_q_dim_taylor_model_result_square radii inner) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_square] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-square";;

let candle_q_dim_taylor_model_program_fixed_step_inv = prove
 (`!center_boxes boxes radii inner stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_inv Candle_analytic_program_inv
       (CONS inner stack) =
     CONS (candle_q_dim_taylor_model_result_inv radii inner) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_inv] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-inv";;

let candle_q_dim_taylor_model_program_fixed_step_sqrt = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_boxes boxes radii inner stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       (Candle_analytic_program_sqrt
         (candle_analytic_sqrt_interval clp cln cld cup cun cud))
       (Candle_analytic_program_sqrt
         (candle_analytic_sqrt_interval blp bln bld bup bun bud))
       (CONS inner stack) =
     CONS
       (candle_q_dim_taylor_model_result_sqrt radii
         (candle_analytic_sqrt_interval clp cln cld cup cun cud)
         (candle_analytic_sqrt_interval blp bln bld bup bun bud)
         inner) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_sqrt] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-sqrt";;

let candle_q_dim_taylor_model_program_fixed_step_atn = prove
 (`!center_boxes boxes radii inner stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_atn Candle_analytic_program_atn
       (CONS inner stack) =
     CONS (candle_q_dim_taylor_model_result_atn radii inner) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_atn] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-atn";;

let candle_q_dim_taylor_model_program_fixed_step_pi_half = prove
 (`!center_boxes boxes radii stack.
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       Candle_analytic_program_pi_half Candle_analytic_program_pi_half stack =
     CONS
       (candle_q_dim_taylor_model_result_pi_half
         radii center_boxes boxes) stack`,
  REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_dim_taylor_model_program_step_pi_half] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE step-lemmas";;

let candle_q_dim_taylor_model_program_fixed_run_append_single = prove
 (`!center_program box_program center_instruction box_instruction
      center_boxes boxes radii stack inner result.
     LENGTH center_program = LENGTH box_program /\
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       center_program box_program stack = CONS inner stack /\
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       center_instruction box_instruction (CONS inner stack) =
       CONS result stack
     ==>
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       (APPEND center_program [center_instruction])
       (APPEND box_program [box_instruction]) stack = CONS result stack`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "length")
      (CONJUNCTS_THEN2 (LABEL_TAC "run") (LABEL_TAC "step"))) THEN
  USE_THEN "length"
    (fun length_th ->
      ONCE_REWRITE_TAC
       [MATCH_MP candle_q_dim_taylor_model_program_fixed_run_append
         length_th]) THEN
  ASM_REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_run_def; APPEND]);;

let candle_q_dim_taylor_model_program_fixed_run_append_binary = prove
 (`!center_left box_left center_right box_right
      center_instruction box_instruction center_boxes boxes radii stack
      left right result.
     LENGTH center_left = LENGTH box_left /\
     LENGTH center_right = LENGTH box_right /\
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       center_left box_left stack = CONS left stack /\
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       center_right box_right (CONS left stack) =
       CONS right (CONS left stack) /\
     candle_q_dim_taylor_model_program_fixed_step center_boxes boxes radii
       center_instruction box_instruction
       (CONS right (CONS left stack)) = CONS result stack
     ==>
     candle_q_dim_taylor_model_program_fixed_run center_boxes boxes radii
       (APPEND center_left (APPEND center_right [center_instruction]))
       (APPEND box_left (APPEND box_right [box_instruction])) stack =
       CONS result stack`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "left_run")
          (CONJUNCTS_THEN2 (LABEL_TAC "right_run")
            (LABEL_TAC "step"))))) THEN
  USE_THEN "left_length"
    (fun length_th ->
      ONCE_REWRITE_TAC
       [MATCH_MP candle_q_dim_taylor_model_program_fixed_run_append
         length_th]) THEN
  USE_THEN "right_length"
    (fun length_th ->
      ONCE_REWRITE_TAC
       [MATCH_MP candle_q_dim_taylor_model_program_fixed_run_append
         length_th]) THEN
  ASM_REWRITE_TAC[candle_q_dim_taylor_model_program_fixed_run_def; APPEND]);;

let _ = print_endline "CANDLE_FIXED_PROGRAM_SOUND_STAGE append-lemmas";;

end;;
