(* ========================================================================== *)
(* Soundness bridge for lazy polynomial completion in the fixed-outer path.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;
open Candle_cv_analytic_expr_fixed_scale_lazy_completion_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy;;
open Candle_cv_whole_box_dim_taylor;;

(* The optimization contract is deliberately restricted to polynomial       *)
(* payloads emitted by the source compiler.  Arbitrary malformed postfix     *)
(* programs are outside this substitution theorem; the established evaluator *)
(* remains the semantic reference for such inputs.                           *)

let candle_analytic_instruction_poly_lazy_exact_def = define
 `(candle_analytic_instruction_poly_lazy_exact center_boxes radii
      (Candle_analytic_push_poly program) <=>
      candle_cv_fs_poly_program_lazy
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_list radii)
        (candle_cv_q_instruction_list program) =
      candle_cv_fs_poly_program
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_list radii)
        (candle_cv_q_instruction_list program)) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      (Candle_analytic_program_sqrt s) <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_neg <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_add <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_mul <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_square <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_inv <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_atn <=> T) /\
  (candle_analytic_instruction_poly_lazy_exact center_boxes radii
      Candle_analytic_program_pi_half <=> T)`;;

let candle_analytic_compile_poly_lazy_exact = prove
 (`!expr center_boxes radii.
     ALL (candle_analytic_instruction_poly_lazy_exact center_boxes radii)
       (candle_analytic_compile expr)`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_compile_def; ALL; ALL_APPEND;
                  candle_analytic_instruction_poly_lazy_exact_def;
                  candle_cv_fs_poly_program_lazy_compile_exact]);;

let candle_cv_fsol_program_step_compiled = prove
 (`!center_instruction box_instruction center_boxes boxes radii stack.
     candle_analytic_instruction_poly_lazy_exact
       center_boxes radii center_instruction
     ==>
     candle_cv_fsol_program_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction) stack =
     candle_cv_fso_program_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction) stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_analytic_instruction_poly_lazy_exact_def;
              candle_cv_fsol_program_step_def;
              candle_cv_fs_q_dim_taylor_model_is_poly_pair_def;
              candle_cv_fso_program_step_def;
              candle_cv_analytic_instruction_def;
              candle_cv_bool_and_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def;
              distinctness "cval"; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_cv_fsol_program_run_compiled = prove
 (`!center_program box_program center_boxes boxes radii stack.
     ALL
       (candle_analytic_instruction_poly_lazy_exact center_boxes radii)
       center_program
     ==>
     candle_cv_fsol_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program) stack =
     candle_cv_fso_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program) stack`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_fsol_program_run_def;
                candle_cv_fso_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[ALL; candle_cv_analytic_instruction_list_def] THEN
    STRIP_TAC THEN
    REWRITE_TAC[candle_cv_fsol_program_run_def;
                candle_cv_fso_program_run_def] THEN
    SUBGOAL_THEN
     `candle_cv_fsol_program_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction h)
        (candle_cv_analytic_instruction h') stack =
      candle_cv_fso_program_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction h)
        (candle_cv_analytic_instruction h') stack`
      SUBST1_TAC THENL
     [MATCH_MP_TAC candle_cv_fsol_program_step_compiled THEN
      ASM_REWRITE_TAC[] THEN
      ALL_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_cv_fsol_program_compiled_exact = prove
 (`!center_e box_e boxes.
     candle_cv_fsol_program
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     candle_cv_fso_program
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsol_program_def; candle_cv_fso_program_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_fixed_list_round_upper_correct] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC candle_cv_fsol_program_run_compiled THEN
  REWRITE_TAC[candle_analytic_compile_poly_lazy_exact]);;

let candle_cv_fsol_certified_check_compiled_exact = prove
 (`!center_e box_e boxes.
     candle_cv_fsol_certified_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     candle_cv_fso_certified_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes)`,
  REWRITE_TAC[candle_cv_fsol_certified_check_def;
              candle_cv_fso_certified_check_def;
              candle_cv_fsol_program_compiled_exact]);;

let candle_cv_fsol_certified_check_correct = prove
 (`!center_e box_e boxes.
     candle_cv_fsol_certified_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile center_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_taylor_model_result_domain
               (candle_q_dim_taylor_model_program_fixed_outer
                 (candle_analytic_compile center_e)
                 (candle_analytic_compile box_e) boxes) /\
             candle_q_box_valid_list boxes /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_taylor_model_certified_upper
                  (candle_q_dim_taylor_model_program_fixed_outer
                    (candle_analytic_compile center_e)
                    (candle_analytic_compile box_e) boxes)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_taylor_model_certified_upper
           (candle_q_dim_taylor_model_program_fixed_outer
             (candle_analytic_compile center_e)
             (candle_analytic_compile box_e) boxes)))`,
  REWRITE_TAC[candle_cv_fsol_certified_check_compiled_exact;
              candle_cv_fso_certified_check_correct]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_LAZY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
